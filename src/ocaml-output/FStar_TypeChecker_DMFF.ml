open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tcenv
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> subst1
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with | { tcenv; subst = subst1; tc_const;_} -> tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { tcenv = env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl))
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___28_1495 = a  in
              let uu____1506 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___28_1495.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___28_1495.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____1506
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____1527 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____1527
             then
               (d "Elaborating extra WP combinators";
                (let uu____1533 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____1533))
             else ());
            (let rec collect_binders t =
               let uu____1565 =
                 let uu____1566 =
                   let uu____1577 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____1577
                    in
                 uu____1566.FStar_Syntax_Syntax.n  in
               match uu____1565 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____1663) -> t1
                     | uu____1680 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____1686 = collect_binders rest  in
                   FStar_List.append bs uu____1686
               | FStar_Syntax_Syntax.Tm_type uu____1711 -> []
               | uu____1723 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____1768 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____1768 FStar_Syntax_Util.name_binders
                in
             (let uu____1809 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____1809
              then
                let uu____1813 =
                  let uu____1815 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____1815  in
                d uu____1813
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____2008 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____2008 with
                | (sigelt,fv) ->
                    ((let uu____2047 =
                        let uu____2055 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____2055
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____2047);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____2185  ->
                     match uu____2185 with
                     | (t,b) ->
                         let uu____2219 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____2219))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____2288 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____2288))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____2347 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____2347)
                 in
              let uu____2363 =
                let uu____2450 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____2525 =
                        let uu____2536 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____2536  in
                      FStar_Syntax_Util.arrow gamma uu____2525  in
                    let uu____2545 =
                      let uu____2546 =
                        let uu____2560 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____2572 =
                          let uu____2586 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____2586]  in
                        uu____2560 :: uu____2572  in
                      FStar_List.append binders uu____2546  in
                    FStar_Syntax_Util.abs uu____2545 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____2649 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____2658 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____2649, uu____2658)  in
                match uu____2450 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____2854 =
                        let uu____2855 =
                          let uu____2880 =
                            let uu____2895 =
                              FStar_List.map
                                (fun uu____2930  ->
                                   match uu____2930 with
                                   | (bv,uu____2951) ->
                                       let uu____2966 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____2975 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____2966, uu____2975)) binders
                               in
                            let uu____2981 =
                              let uu____2992 =
                                let uu____3001 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____3010 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____3001, uu____3010)  in
                              let uu____3016 =
                                let uu____3027 =
                                  let uu____3036 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____3036)  in
                                [uu____3027]  in
                              uu____2992 :: uu____3016  in
                            FStar_List.append uu____2895 uu____2981  in
                          (fv, uu____2880)  in
                        FStar_Syntax_Syntax.Tm_app uu____2855  in
                      mk1 uu____2854  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____2363 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____3395 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____3395
                       in
                    let ret1 =
                      let uu____3415 =
                        let uu____3430 =
                          let uu____3441 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____3441  in
                        FStar_Syntax_Util.residual_tot uu____3430  in
                      FStar_Pervasives_Native.Some uu____3415  in
                    let body =
                      let uu____3468 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____3468 ret1  in
                    let uu____3479 =
                      let uu____3480 = mk_all_implicit binders  in
                      let uu____3492 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____3480 uu____3492  in
                    FStar_Syntax_Util.abs uu____3479 body ret1  in
                  let c_pure1 =
                    let uu____3583 = mk_lid "pure"  in
                    register env1 uu____3583 c_pure  in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let l =
                      let uu____3639 =
                        let uu____3648 =
                          let uu____3657 =
                            let uu____3671 =
                              let uu____3683 =
                                let uu____3694 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____3694
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____3683  in
                            [uu____3671]  in
                          let uu____3725 =
                            let uu____3736 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____3736  in
                          FStar_Syntax_Util.arrow uu____3657 uu____3725  in
                        mk_gctx uu____3648  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____3639
                       in
                    let r =
                      let uu____3757 =
                        let uu____3766 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____3766  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____3757
                       in
                    let ret1 =
                      let uu____3786 =
                        let uu____3801 =
                          let uu____3812 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____3812  in
                        FStar_Syntax_Util.residual_tot uu____3801  in
                      FStar_Pervasives_Native.Some uu____3786  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____3853 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____3864 =
                          let uu____3879 =
                            let uu____3882 =
                              let uu____3883 =
                                let uu____3892 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____3892
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____3883  in
                            [uu____3882]  in
                          FStar_List.append gamma_as_args uu____3879  in
                        FStar_Syntax_Util.mk_app uu____3853 uu____3864  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____3903 =
                      let uu____3904 = mk_all_implicit binders  in
                      let uu____3916 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____3904 uu____3916  in
                    FStar_Syntax_Util.abs uu____3903 outer_body ret1  in
                  let c_app1 =
                    let uu____4041 = mk_lid "app"  in
                    register env1 uu____4041 c_app  in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____4097 =
                        let uu____4111 =
                          let uu____4123 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____4123  in
                        [uu____4111]  in
                      let uu____4154 =
                        let uu____4165 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____4165  in
                      FStar_Syntax_Util.arrow uu____4097 uu____4154  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____4197 =
                        let uu____4206 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____4206  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____4197
                       in
                    let ret1 =
                      let uu____4226 =
                        let uu____4241 =
                          let uu____4252 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____4252  in
                        FStar_Syntax_Util.residual_tot uu____4241  in
                      FStar_Pervasives_Native.Some uu____4226  in
                    let uu____4268 =
                      let uu____4269 = mk_all_implicit binders  in
                      let uu____4281 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____4269 uu____4281  in
                    let uu____4397 =
                      let uu____4408 =
                        let uu____4423 =
                          let uu____4430 =
                            let uu____4439 =
                              let uu____4454 =
                                let uu____4461 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____4461]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____4454
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____4439  in
                          let uu____4494 =
                            let uu____4501 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____4501]  in
                          uu____4430 :: uu____4494  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____4423
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____4408  in
                    FStar_Syntax_Util.abs uu____4268 uu____4397 ret1  in
                  let c_lift11 =
                    let uu____4547 = mk_lid "lift1"  in
                    register env1 uu____4547 c_lift1  in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____4615 =
                        let uu____4629 =
                          let uu____4641 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____4641  in
                        let uu____4650 =
                          let uu____4664 =
                            let uu____4676 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____4676  in
                          [uu____4664]  in
                        uu____4629 :: uu____4650  in
                      let uu____4718 =
                        let uu____4729 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____4729  in
                      FStar_Syntax_Util.arrow uu____4615 uu____4718  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____4761 =
                        let uu____4770 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____4770  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____4761
                       in
                    let a2 =
                      let uu____4791 =
                        let uu____4800 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____4800  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____4791
                       in
                    let ret1 =
                      let uu____4820 =
                        let uu____4835 =
                          let uu____4846 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____4846  in
                        FStar_Syntax_Util.residual_tot uu____4835  in
                      FStar_Pervasives_Native.Some uu____4820  in
                    let uu____4862 =
                      let uu____4863 = mk_all_implicit binders  in
                      let uu____4875 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____4863 uu____4875  in
                    let uu____5025 =
                      let uu____5036 =
                        let uu____5051 =
                          let uu____5058 =
                            let uu____5067 =
                              let uu____5082 =
                                let uu____5089 =
                                  let uu____5098 =
                                    let uu____5113 =
                                      let uu____5120 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____5120]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____5113
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____5098
                                   in
                                let uu____5153 =
                                  let uu____5160 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____5160]  in
                                uu____5089 :: uu____5153  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____5082
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____5067  in
                          let uu____5197 =
                            let uu____5204 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____5204]  in
                          uu____5058 :: uu____5197  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____5051
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____5036  in
                    FStar_Syntax_Util.abs uu____4862 uu____5025 ret1  in
                  let c_lift21 =
                    let uu____5250 = mk_lid "lift2"  in
                    register env1 uu____5250 c_lift2  in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____5306 =
                        let uu____5320 =
                          let uu____5332 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____5332  in
                        [uu____5320]  in
                      let uu____5363 =
                        let uu____5374 =
                          let uu____5383 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____5383  in
                        FStar_Syntax_Syntax.mk_Total uu____5374  in
                      FStar_Syntax_Util.arrow uu____5306 uu____5363  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____5414 =
                        let uu____5429 =
                          let uu____5440 =
                            let uu____5449 =
                              let uu____5463 =
                                let uu____5475 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____5475
                                 in
                              [uu____5463]  in
                            let uu____5506 =
                              let uu____5517 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____5517  in
                            FStar_Syntax_Util.arrow uu____5449 uu____5506  in
                          mk_ctx uu____5440  in
                        FStar_Syntax_Util.residual_tot uu____5429  in
                      FStar_Pervasives_Native.Some uu____5414  in
                    let e1 =
                      let uu____5544 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____5544
                       in
                    let body =
                      let uu____5565 =
                        let uu____5566 =
                          let uu____5580 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____5580]  in
                        FStar_List.append gamma uu____5566  in
                      let uu____5625 =
                        let uu____5636 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____5647 =
                          let uu____5662 =
                            let uu____5663 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____5663  in
                          let uu____5672 = args_of_binders1 gamma  in
                          uu____5662 :: uu____5672  in
                        FStar_Syntax_Util.mk_app uu____5636 uu____5647  in
                      FStar_Syntax_Util.abs uu____5565 uu____5625 ret1  in
                    let uu____5675 =
                      let uu____5676 = mk_all_implicit binders  in
                      let uu____5688 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____5676 uu____5688  in
                    FStar_Syntax_Util.abs uu____5675 body ret1  in
                  let c_push1 =
                    let uu____5796 = mk_lid "push"  in
                    register env1 uu____5796 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____5866 =
                        let uu____5867 =
                          let uu____5892 = args_of_binders1 binders  in
                          (c, uu____5892)  in
                        FStar_Syntax_Syntax.Tm_app uu____5867  in
                      mk1 uu____5866
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____5949 =
                        let uu____5958 =
                          let uu____5972 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____5984 =
                            let uu____5998 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____5998]  in
                          uu____5972 :: uu____5984  in
                        let uu____6043 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____5958 uu____6043  in
                      FStar_Syntax_Syntax.mk_Total uu____5949  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____6066 =
                      let uu____6067 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____6067  in
                    let uu____6107 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____6128 =
                        let uu____6139 =
                          let uu____6154 =
                            let uu____6161 =
                              let uu____6170 =
                                let uu____6185 =
                                  let uu____6198 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____6198  in
                                [uu____6185]  in
                              FStar_Syntax_Util.mk_app l_ite uu____6170  in
                            [uu____6161]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____6154
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____6139  in
                      FStar_Syntax_Util.ascribe uu____6128
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____6066 uu____6107
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____6313 = mk_lid "wp_if_then_else"  in
                    register env1 uu____6313 wp_if_then_else  in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1  in
                  let wp_assert =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_and =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.and_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____6390 =
                        let uu____6405 =
                          let uu____6412 =
                            let uu____6421 =
                              let uu____6436 =
                                let uu____6443 =
                                  let uu____6452 =
                                    let uu____6467 =
                                      let uu____6480 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____6480
                                       in
                                    [uu____6467]  in
                                  FStar_Syntax_Util.mk_app l_and uu____6452
                                   in
                                [uu____6443]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____6436
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____6421  in
                          let uu____6537 =
                            let uu____6544 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____6544]  in
                          uu____6412 :: uu____6537  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____6405
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____6390  in
                    let uu____6581 =
                      let uu____6582 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____6582  in
                    FStar_Syntax_Util.abs uu____6581 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____6636 = mk_lid "wp_assert"  in
                    register env1 uu____6636 wp_assert  in
                  let wp_assert2 = mk_generic_app wp_assert1  in
                  let wp_assume =
                    let q =
                      FStar_Syntax_Syntax.gen_bv "q"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let l_imp =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
                        (FStar_Syntax_Syntax.Delta_constant_at_level
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____6713 =
                        let uu____6728 =
                          let uu____6735 =
                            let uu____6744 =
                              let uu____6759 =
                                let uu____6766 =
                                  let uu____6775 =
                                    let uu____6790 =
                                      let uu____6803 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____6803
                                       in
                                    [uu____6790]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____6775
                                   in
                                [uu____6766]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____6759
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____6744  in
                          let uu____6860 =
                            let uu____6867 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____6867]  in
                          uu____6735 :: uu____6860  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____6728
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____6713  in
                    let uu____6904 =
                      let uu____6905 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____6905  in
                    FStar_Syntax_Util.abs uu____6904 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____6959 = mk_lid "wp_assume"  in
                    register env1 uu____6959 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____7014 =
                        let uu____7028 =
                          let uu____7040 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____7040  in
                        [uu____7028]  in
                      let uu____7071 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____7014 uu____7071  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____7105 =
                        let uu____7120 =
                          let uu____7127 =
                            let uu____7136 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____7136  in
                          let uu____7175 =
                            let uu____7182 =
                              let uu____7191 =
                                let uu____7206 =
                                  let uu____7213 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____7213]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____7206
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____7191  in
                            [uu____7182]  in
                          uu____7127 :: uu____7175  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____7120
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____7105  in
                    let uu____7274 =
                      let uu____7275 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____7275  in
                    FStar_Syntax_Util.abs uu____7274 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____7329 = mk_lid "wp_close"  in
                    register env1 uu____7329 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____7377 =
                      let uu____7392 =
                        let uu____7409 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____7409
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____7392  in
                    FStar_Pervasives_Native.Some uu____7377  in
                  let mk_forall1 x body =
                    let uu____7474 =
                      let uu____7481 =
                        let uu____7482 =
                          let uu____7507 =
                            let uu____7522 =
                              let uu____7535 =
                                let uu____7544 =
                                  let uu____7545 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____7545]  in
                                FStar_Syntax_Util.abs uu____7544 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____7535  in
                            [uu____7522]  in
                          (FStar_Syntax_Util.tforall, uu____7507)  in
                        FStar_Syntax_Syntax.Tm_app uu____7482  in
                      FStar_Syntax_Syntax.mk uu____7481  in
                    uu____7474 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____7642 =
                      let uu____7643 = FStar_Syntax_Subst.compress t  in
                      uu____7643.FStar_Syntax_Syntax.n  in
                    match uu____7642 with
                    | FStar_Syntax_Syntax.Tm_type uu____7655 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____7711  ->
                              match uu____7711 with
                              | (b,uu____7725) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____7740 -> true  in
                  let rec is_monotonic t =
                    let uu____7761 =
                      let uu____7762 = FStar_Syntax_Subst.compress t  in
                      uu____7762.FStar_Syntax_Syntax.n  in
                    match uu____7761 with
                    | FStar_Syntax_Syntax.Tm_type uu____7774 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____7830  ->
                              match uu____7830 with
                              | (b,uu____7844) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____7859 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____8009 =
                      let uu____8010 = FStar_Syntax_Subst.compress t1  in
                      uu____8010.FStar_Syntax_Syntax.n  in
                    match uu____8009 with
                    | FStar_Syntax_Syntax.Tm_type uu____8027 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____8030);
                                      FStar_Syntax_Syntax.pos = uu____8031;
                                      FStar_Syntax_Syntax.vars = uu____8032;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____8125 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____8125
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____8157 =
                              let uu____8168 =
                                let uu____8183 =
                                  let uu____8196 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____8196  in
                                [uu____8183]  in
                              FStar_Syntax_Util.mk_app x uu____8168  in
                            let uu____8229 =
                              let uu____8240 =
                                let uu____8255 =
                                  let uu____8268 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____8268  in
                                [uu____8255]  in
                              FStar_Syntax_Util.mk_app y uu____8240  in
                            mk_rel1 b uu____8157 uu____8229  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____8336 =
                               let uu____8347 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____8358 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____8347 uu____8358  in
                             let uu____8369 =
                               let uu____8380 =
                                 let uu____8391 =
                                   let uu____8406 =
                                     let uu____8419 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____8419
                                      in
                                   [uu____8406]  in
                                 FStar_Syntax_Util.mk_app x uu____8391  in
                               let uu____8452 =
                                 let uu____8463 =
                                   let uu____8478 =
                                     let uu____8491 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____8491
                                      in
                                   [uu____8478]  in
                                 FStar_Syntax_Util.mk_app y uu____8463  in
                               mk_rel1 b uu____8380 uu____8452  in
                             FStar_Syntax_Util.mk_imp uu____8336 uu____8369
                              in
                           let uu____8524 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____8524)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____8535);
                                      FStar_Syntax_Syntax.pos = uu____8536;
                                      FStar_Syntax_Syntax.vars = uu____8537;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____8630 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____8630
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____8662 =
                              let uu____8673 =
                                let uu____8688 =
                                  let uu____8701 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____8701  in
                                [uu____8688]  in
                              FStar_Syntax_Util.mk_app x uu____8673  in
                            let uu____8734 =
                              let uu____8745 =
                                let uu____8760 =
                                  let uu____8773 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____8773  in
                                [uu____8760]  in
                              FStar_Syntax_Util.mk_app y uu____8745  in
                            mk_rel1 b uu____8662 uu____8734  in
                          mk_forall1 a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2
                              in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2
                              in
                           let body =
                             let uu____8841 =
                               let uu____8852 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____8863 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____8852 uu____8863  in
                             let uu____8874 =
                               let uu____8885 =
                                 let uu____8896 =
                                   let uu____8911 =
                                     let uu____8924 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____8924
                                      in
                                   [uu____8911]  in
                                 FStar_Syntax_Util.mk_app x uu____8896  in
                               let uu____8957 =
                                 let uu____8968 =
                                   let uu____8983 =
                                     let uu____8996 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____8996
                                      in
                                   [uu____8983]  in
                                 FStar_Syntax_Util.mk_app y uu____8968  in
                               mk_rel1 b uu____8885 uu____8957  in
                             FStar_Syntax_Util.mk_imp uu____8841 uu____8874
                              in
                           let uu____9029 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____9029)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___242_9112 = t1  in
                          let uu____9121 =
                            let uu____9122 =
                              let uu____9146 =
                                let uu____9157 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____9157  in
                              ([binder], uu____9146)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____9122  in
                          {
                            FStar_Syntax_Syntax.n = uu____9121;
                            FStar_Syntax_Syntax.pos =
                              (uu___242_9112.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___242_9112.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____9207 ->
                        failwith "unhandled arrow"
                    | uu____9238 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env1 t
                         in
                      let uu____9339 =
                        let uu____9340 = FStar_Syntax_Subst.compress t1  in
                        uu____9340.FStar_Syntax_Syntax.n  in
                      match uu____9339 with
                      | FStar_Syntax_Syntax.Tm_type uu____9355 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____9398 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____9398
                          ->
                          let project i tuple =
                            let projector =
                              let uu____9447 =
                                let uu____9456 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____9456 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____9447
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____9510 =
                            let uu____9529 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____9559  ->
                                     match uu____9559 with
                                     | (t2,q) ->
                                         let uu____9595 = project i x  in
                                         let uu____9606 = project i y  in
                                         mk_stronger t2 uu____9595 uu____9606)
                                args
                               in
                            match uu____9529 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____9510 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____9736);
                                      FStar_Syntax_Syntax.pos = uu____9737;
                                      FStar_Syntax_Syntax.vars = uu____9738;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____9823  ->
                                   match uu____9823 with
                                   | (bv,q) ->
                                       let uu____9857 =
                                         let uu____9859 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____9859  in
                                       FStar_Syntax_Syntax.gen_bv uu____9857
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____9878 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____9878) bvs
                             in
                          let body =
                            let uu____9896 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____9907 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____9896 uu____9907  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____9942);
                                      FStar_Syntax_Syntax.pos = uu____9943;
                                      FStar_Syntax_Syntax.vars = uu____9944;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____10029  ->
                                   match uu____10029 with
                                   | (bv,q) ->
                                       let uu____10063 =
                                         let uu____10065 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____10065  in
                                       FStar_Syntax_Syntax.gen_bv uu____10063
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____10084 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____10084) bvs
                             in
                          let body =
                            let uu____10102 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____10113 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____10102 uu____10113  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____10146 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____10161 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____10172 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____10183 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____10161 uu____10172 uu____10183  in
                    let uu____10194 =
                      let uu____10195 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____10195  in
                    FStar_Syntax_Util.abs uu____10194 body ret_tot_type  in
                  let stronger1 =
                    let uu____10290 = mk_lid "stronger"  in
                    register env1 uu____10290 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____10332 = FStar_Util.prefix gamma  in
                    match uu____10332 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____10476 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____10476
                             in
                          let uu____10494 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____10494 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____10524 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____10524  in
                              let guard_free1 =
                                let uu____10548 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____10548  in
                              let pat =
                                let uu____10566 =
                                  let uu____10581 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____10581]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____10566
                                 in
                              let pattern_guarded_body =
                                let uu____10629 =
                                  let uu____10630 =
                                    let uu____10641 =
                                      let uu____10642 =
                                        let uu____10671 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1
                                           in
                                        let uu____10680 =
                                          let uu____10697 =
                                            let uu____10712 =
                                              FStar_Syntax_Syntax.as_arg pat
                                               in
                                            [uu____10712]  in
                                          [uu____10697]  in
                                        (uu____10671, uu____10680)  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____10642
                                       in
                                    (body, uu____10641)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____10630  in
                                mk1 uu____10629  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____10807 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____10828 =
                            let uu____10839 =
                              let uu____10848 =
                                let uu____10859 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____10870 =
                                  let uu____10885 = args_of_binders1 wp_args
                                     in
                                  let uu____10888 =
                                    let uu____10891 =
                                      let uu____10892 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____10892
                                       in
                                    [uu____10891]  in
                                  FStar_List.append uu____10885 uu____10888
                                   in
                                FStar_Syntax_Util.mk_app uu____10859
                                  uu____10870
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____10848  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____10839
                             in
                          FStar_Syntax_Util.abs gamma uu____10828
                            ret_gtot_type
                           in
                        let uu____10901 =
                          let uu____10902 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____10902  in
                        FStar_Syntax_Util.abs uu____10901 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____10951 = mk_lid "ite_wp"  in
                    register env1 uu____10951 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____10993 = FStar_Util.prefix gamma  in
                    match uu____10993 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____11108 =
                            let uu____11117 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____11146 =
                              let uu____11161 =
                                let uu____11174 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____11174  in
                              [uu____11161]  in
                            FStar_Syntax_Util.mk_app uu____11117 uu____11146
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____11108
                           in
                        let uu____11207 =
                          let uu____11208 =
                            let uu____11222 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____11222 gamma  in
                          FStar_List.append binders uu____11208  in
                        FStar_Syntax_Util.abs uu____11207 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____11277 = mk_lid "null_wp"  in
                    register env1 uu____11277 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____11332 =
                        let uu____11347 =
                          let uu____11354 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____11363 =
                            let uu____11370 =
                              let uu____11379 =
                                let uu____11394 =
                                  let uu____11407 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____11407  in
                                [uu____11394]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____11379
                               in
                            let uu____11440 =
                              let uu____11447 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____11447]  in
                            uu____11370 :: uu____11440  in
                          uu____11354 :: uu____11363  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____11347
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____11332  in
                    let uu____11488 =
                      let uu____11489 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____11489  in
                    FStar_Syntax_Util.abs uu____11488 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____11538 = mk_lid "wp_trivial"  in
                    register env1 uu____11538 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____11560 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____11560
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____11580 =
                      let uu____11581 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____11581  in
                    let uu____11627 =
                      let uu___349_11668 = ed  in
                      let uu____11709 =
                        let uu____11710 = c wp_if_then_else2  in
                        ([], uu____11710)  in
                      let uu____11733 =
                        let uu____11734 = c ite_wp2  in ([], uu____11734)  in
                      let uu____11757 =
                        let uu____11758 = c stronger2  in ([], uu____11758)
                         in
                      let uu____11781 =
                        let uu____11782 = c wp_close2  in ([], uu____11782)
                         in
                      let uu____11805 =
                        let uu____11806 = c wp_assert2  in ([], uu____11806)
                         in
                      let uu____11829 =
                        let uu____11830 = c wp_assume2  in ([], uu____11830)
                         in
                      let uu____11853 =
                        let uu____11854 = c null_wp2  in ([], uu____11854)
                         in
                      let uu____11877 =
                        let uu____11878 = c wp_trivial2  in ([], uu____11878)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___349_11668.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___349_11668.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___349_11668.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___349_11668.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___349_11668.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___349_11668.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___349_11668.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____11709;
                        FStar_Syntax_Syntax.ite_wp = uu____11733;
                        FStar_Syntax_Syntax.stronger = uu____11757;
                        FStar_Syntax_Syntax.close_wp = uu____11781;
                        FStar_Syntax_Syntax.assert_p = uu____11805;
                        FStar_Syntax_Syntax.assume_p = uu____11829;
                        FStar_Syntax_Syntax.null_wp = uu____11853;
                        FStar_Syntax_Syntax.trivial = uu____11877;
                        FStar_Syntax_Syntax.repr =
                          (uu___349_11668.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___349_11668.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___349_11668.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___349_11668.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___349_11668.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____11580, uu____11627)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___354_12442 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___354_12442.subst);
        tc_const = (uu___354_12442.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____12589 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____12632 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____12680) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___0_12707  ->
                match uu___0_12707 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____12710 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____12712 ->
        let uu____12713 =
          let uu____12719 =
            let uu____12721 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____12721
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____12719)  in
        FStar_Errors.raise_error uu____12713 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___1_12731  ->
    match uu___1_12731 with
    | N t ->
        let uu____12738 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____12738
    | M t ->
        let uu____12746 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____12746
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____12755,c) -> nm_of_comp c
    | uu____12795 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____12816 = nm_of_comp c  in
    match uu____12816 with | M uu____12818 -> true | N uu____12824 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____12839 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____12879 =
        let uu____12893 =
          let uu____12905 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____12905  in
        [uu____12893]  in
      let uu____12954 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____12879 uu____12954  in
    let uu____12965 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____12965
  
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        let uu____13230 =
          let uu____13231 =
            let uu____13255 =
              let uu____13269 =
                let uu____13281 =
                  let uu____13292 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____13292  in
                let uu____13301 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____13281, uu____13301)  in
              [uu____13269]  in
            let uu____13334 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____13255, uu____13334)  in
          FStar_Syntax_Syntax.Tm_arrow uu____13231  in
        mk1 uu____13230

and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
         in
      let mk_star_to_type1 = mk_star_to_type mk1  in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____13533) ->
          let binders1 =
            FStar_List.map
              (fun uu____13612  ->
                 match uu____13612 with
                 | (bv,aqual) ->
                     let uu____13651 =
                       let uu___404_13662 = bv  in
                       let uu____13673 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___404_13662.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___404_13662.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____13673
                       }  in
                     (uu____13651, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____13695,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____13697);
                              FStar_Syntax_Syntax.pos = uu____13698;
                              FStar_Syntax_Syntax.vars = uu____13699;_})
               ->
               let uu____13754 =
                 let uu____13755 =
                   let uu____13779 =
                     let uu____13790 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____13790  in
                   (binders1, uu____13779)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____13755  in
               mk1 uu____13754
           | uu____13818 ->
               let uu____13819 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____13819 with
                | N hn ->
                    let uu____13829 =
                      let uu____13830 =
                        let uu____13854 =
                          let uu____13865 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____13865  in
                        (binders1, uu____13854)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____13830  in
                    mk1 uu____13829
                | M a ->
                    let uu____13898 =
                      let uu____13899 =
                        let uu____13923 =
                          let uu____13937 =
                            let uu____13951 =
                              let uu____13963 =
                                let uu____13974 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____13974  in
                              let uu____13983 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____13963, uu____13983)  in
                            [uu____13951]  in
                          FStar_List.append binders1 uu____13937  in
                        let uu____14027 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____13923, uu____14027)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____13899  in
                    mk1 uu____13898))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____14222 = f x  in
                    FStar_Util.string_builder_append strb uu____14222);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____14241 = f x1  in
                         FStar_Util.string_builder_append strb uu____14241))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____14245 =
              let uu____14251 =
                let uu____14253 = FStar_Syntax_Print.term_to_string t2  in
                let uu____14255 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____14253 uu____14255
                 in
              (FStar_Errors.Warning_DependencyFound, uu____14251)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____14245  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____14285 =
              let uu____14286 = FStar_Syntax_Subst.compress ty  in
              uu____14286.FStar_Syntax_Syntax.n  in
            match uu____14285 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____14338 =
                  let uu____14340 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____14340  in
                if uu____14338
                then false
                else
                  (try
                     (fun uu___453_14357  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____14404 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____14404 s  in
                              let uu____14417 =
                                let uu____14419 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____14419  in
                              if uu____14417
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____14430 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____14430 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____14482  ->
                                          match uu____14482 with
                                          | (bv,uu____14509) ->
                                              (non_dependent_or_raise s
                                                 bv.FStar_Syntax_Syntax.sort;
                                               FStar_Util.set_add bv s))
                                     FStar_Syntax_Syntax.no_names binders1
                                    in
                                 let ct = FStar_Syntax_Util.comp_result c1
                                    in
                                 (non_dependent_or_raise s ct;
                                  (let k = n1 - (FStar_List.length binders1)
                                      in
                                   if k > (Prims.parse_int "0")
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found  -> false)
            | uu____14565 ->
                ((let uu____14567 =
                    let uu____14573 =
                      let uu____14575 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____14575
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____14573)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____14567);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____14599 =
              let uu____14600 = FStar_Syntax_Subst.compress head2  in
              uu____14600.FStar_Syntax_Syntax.n  in
            match uu____14599 with
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
                  (let uu____14617 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____14617)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____14631 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____14631 with
                 | ((uu____14649,ty),uu____14651) ->
                     let uu____14668 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____14668
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____14693 =
                         let uu____14694 = FStar_Syntax_Subst.compress res
                            in
                         uu____14694.FStar_Syntax_Syntax.n  in
                       (match uu____14693 with
                        | FStar_Syntax_Syntax.Tm_app uu____14706 -> true
                        | uu____14732 ->
                            ((let uu____14734 =
                                let uu____14740 =
                                  let uu____14742 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____14742
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____14740)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____14734);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____14750 -> true
            | FStar_Syntax_Syntax.Tm_name uu____14757 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____14765) ->
                is_valid_application t2
            | uu____14778 -> false  in
          let uu____14780 = is_valid_application head1  in
          if uu____14780
          then
            let uu____14787 =
              let uu____14788 =
                let uu____14813 =
                  FStar_List.map
                    (fun uu____14854  ->
                       match uu____14854 with
                       | (t2,qual) ->
                           let uu____14895 = star_type' env t2  in
                           (uu____14895, qual)) args
                   in
                (head1, uu____14813)  in
              FStar_Syntax_Syntax.Tm_app uu____14788  in
            mk1 uu____14787
          else
            (let uu____14932 =
               let uu____14938 =
                 let uu____14940 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____14940
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____14938)  in
             FStar_Errors.raise_err uu____14932)
      | FStar_Syntax_Syntax.Tm_bvar uu____14948 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____14954 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____14960 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____14961 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____15024 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____15024 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___525_15162 = env  in
                 let uu____15277 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____15277;
                   subst = (uu___525_15162.subst);
                   tc_const = (uu___525_15162.tc_const)
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
               ((let uu___540_15499 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___540_15499.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___540_15499.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____15524 =
            let uu____15525 =
              let uu____15536 = star_type' env t2  in (uu____15536, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____15525  in
          mk1 uu____15524
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____15656 =
            let uu____15657 =
              let uu____15704 = star_type' env e  in
              let uu____15715 =
                let uu____15744 =
                  let uu____15761 = star_type' env t2  in
                  FStar_Util.Inl uu____15761  in
                (uu____15744, FStar_Pervasives_Native.None)  in
              (uu____15704, uu____15715, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____15657  in
          mk1 uu____15656
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____15957 =
            let uu____15958 =
              let uu____16005 = star_type' env e  in
              let uu____16016 =
                let uu____16045 =
                  let uu____16062 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____16062  in
                (uu____16045, FStar_Pervasives_Native.None)  in
              (uu____16005, uu____16016, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____15958  in
          mk1 uu____15957
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____16155,(uu____16156,FStar_Pervasives_Native.Some uu____16157),uu____16158)
          ->
          let uu____16263 =
            let uu____16269 =
              let uu____16271 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____16271
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16269)  in
          FStar_Errors.raise_err uu____16263
      | FStar_Syntax_Syntax.Tm_refine uu____16279 ->
          let uu____16295 =
            let uu____16301 =
              let uu____16303 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____16303
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16301)  in
          FStar_Errors.raise_err uu____16295
      | FStar_Syntax_Syntax.Tm_uinst uu____16311 ->
          let uu____16322 =
            let uu____16328 =
              let uu____16330 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____16330
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16328)  in
          FStar_Errors.raise_err uu____16322
      | FStar_Syntax_Syntax.Tm_quoted uu____16338 ->
          let uu____16351 =
            let uu____16357 =
              let uu____16359 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____16359
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16357)  in
          FStar_Errors.raise_err uu____16351
      | FStar_Syntax_Syntax.Tm_constant uu____16367 ->
          let uu____16368 =
            let uu____16374 =
              let uu____16376 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____16376
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16374)  in
          FStar_Errors.raise_err uu____16368
      | FStar_Syntax_Syntax.Tm_match uu____16384 ->
          let uu____16422 =
            let uu____16428 =
              let uu____16430 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____16430
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16428)  in
          FStar_Errors.raise_err uu____16422
      | FStar_Syntax_Syntax.Tm_let uu____16438 ->
          let uu____16463 =
            let uu____16469 =
              let uu____16471 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____16471
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16469)  in
          FStar_Errors.raise_err uu____16463
      | FStar_Syntax_Syntax.Tm_uvar uu____16479 ->
          let uu____16500 =
            let uu____16506 =
              let uu____16508 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____16508
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16506)  in
          FStar_Errors.raise_err uu____16500
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____16516 =
            let uu____16522 =
              let uu____16524 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____16524
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____16522)  in
          FStar_Errors.raise_err uu____16516
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____16537 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____16537
      | FStar_Syntax_Syntax.Tm_delayed uu____16548 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___3_16599  ->
    match uu___3_16599 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___2_16638  ->
                match uu___2_16638 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____16641 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____16659 =
      let uu____16660 = FStar_Syntax_Subst.compress t  in
      uu____16660.FStar_Syntax_Syntax.n  in
    match uu____16659 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____16716 =
            let uu____16725 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____16725  in
          is_C uu____16716  in
        if r
        then
          ((let uu____16761 =
              let uu____16763 =
                FStar_List.for_all
                  (fun uu____16778  ->
                     match uu____16778 with | (h,uu____16791) -> is_C h) args
                 in
              Prims.op_Negation uu____16763  in
            if uu____16761 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____16812 =
              let uu____16814 =
                FStar_List.for_all
                  (fun uu____16830  ->
                     match uu____16830 with
                     | (h,uu____16843) ->
                         let uu____16856 = is_C h  in
                         Prims.op_Negation uu____16856) args
                 in
              Prims.op_Negation uu____16814  in
            if uu____16812 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____16903 = nm_of_comp comp  in
        (match uu____16903 with
         | M t1 ->
             ((let uu____16911 = is_C t1  in
               if uu____16911 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____16924) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____16938) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____16952,uu____16953) -> is_C t1
    | uu____17034 -> false
  
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun t  ->
      fun e  ->
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
           in
        let p_type = mk_star_to_type mk1 env t  in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type
           in
        let body =
          let uu____17234 =
            let uu____17235 =
              let uu____17260 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____17271 =
                let uu____17286 =
                  let uu____17299 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____17299)  in
                [uu____17286]  in
              (uu____17260, uu____17271)  in
            FStar_Syntax_Syntax.Tm_app uu____17235  in
          mk1 uu____17234  in
        let uu____17355 =
          let uu____17356 = FStar_Syntax_Syntax.mk_binder p  in [uu____17356]
           in
        FStar_Syntax_Util.abs uu____17355 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___4_17403  ->
    match uu___4_17403 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____17406 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____18538 =
          match uu____18538 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____18623 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____18626 =
                       let uu____18628 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____18628  in
                     Prims.op_Negation uu____18626)
                   in
                if uu____18623
                then
                  let uu____18638 =
                    let uu____18644 =
                      let uu____18646 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____18648 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____18650 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____18646 uu____18648 uu____18650
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____18644)  in
                  FStar_Errors.raise_err uu____18638
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____18723 = mk_return env t1 s_e  in
                     ((M t1), uu____18723, u_e)))
               | (M t1,N t2) ->
                   let uu____18754 =
                     let uu____18760 =
                       let uu____18762 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____18764 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____18766 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____18762 uu____18764 uu____18766
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____18760)
                      in
                   FStar_Errors.raise_err uu____18754)
           in
        let ensure_m env1 e2 =
          let strip_m uu___5_18992 =
            match uu___5_18992 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____19060 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____19117 =
                let uu____19123 =
                  let uu____19125 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____19125
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____19123)  in
              FStar_Errors.raise_error uu____19117 e2.FStar_Syntax_Syntax.pos
          | M uu____19147 ->
              let uu____19152 = check env1 e2 context_nm  in
              strip_m uu____19152
           in
        let uu____19167 =
          let uu____19168 = FStar_Syntax_Subst.compress e  in
          uu____19168.FStar_Syntax_Syntax.n  in
        match uu____19167 with
        | FStar_Syntax_Syntax.Tm_bvar uu____19193 ->
            let uu____19199 = infer env e  in return_if uu____19199
        | FStar_Syntax_Syntax.Tm_name uu____19214 ->
            let uu____19220 = infer env e  in return_if uu____19220
        | FStar_Syntax_Syntax.Tm_fvar uu____19235 ->
            let uu____19239 = infer env e  in return_if uu____19239
        | FStar_Syntax_Syntax.Tm_abs uu____19254 ->
            let uu____19289 = infer env e  in return_if uu____19289
        | FStar_Syntax_Syntax.Tm_constant uu____19304 ->
            let uu____19305 = infer env e  in return_if uu____19305
        | FStar_Syntax_Syntax.Tm_quoted uu____19320 ->
            let uu____19333 = infer env e  in return_if uu____19333
        | FStar_Syntax_Syntax.Tm_app uu____19348 ->
            let uu____19373 = infer env e  in return_if uu____19373
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____19393 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____19393 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____19661) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____19675) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____19689,uu____19690) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____19771 ->
            let uu____19796 =
              let uu____19798 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____19798  in
            failwith uu____19796
        | FStar_Syntax_Syntax.Tm_type uu____19815 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____19831 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____19870 ->
            let uu____19886 =
              let uu____19888 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____19888  in
            failwith uu____19886
        | FStar_Syntax_Syntax.Tm_uvar uu____19905 ->
            let uu____19926 =
              let uu____19928 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____19928  in
            failwith uu____19926
        | FStar_Syntax_Syntax.Tm_delayed uu____19945 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____19991 =
              let uu____19993 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____19993  in
            failwith uu____19991

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos
         in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env.tcenv
         in
      let uu____20112 =
        let uu____20113 = FStar_Syntax_Subst.compress e  in
        uu____20113.FStar_Syntax_Syntax.n  in
      match uu____20112 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____20178 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____20178
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____20297;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____20298;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____20340 =
                  let uu___775_20355 = rc  in
                  let uu____20370 =
                    let uu____20379 =
                      let uu____20390 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____20390  in
                    FStar_Pervasives_Native.Some uu____20379  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___775_20355.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____20370;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___775_20355.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____20340
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___781_20554 = env  in
            let uu____20669 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____20669;
              subst = (uu___781_20554.subst);
              tc_const = (uu___781_20554.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____20818  ->
                 match uu____20818 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___788_20874 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___788_20874.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___788_20874.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____20885 =
            FStar_List.fold_left
              (fun uu____21035  ->
                 fun uu____21036  ->
                   match (uu____21035, uu____21036) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____21469 = is_C c  in
                       if uu____21469
                       then
                         let xw =
                           let uu____21546 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____21546
                            in
                         let x =
                           let uu___800_21567 = bv  in
                           let uu____21578 =
                             let uu____21589 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____21589  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___800_21567.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___800_21567.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____21578
                           }  in
                         let env3 =
                           let uu___803_21713 = env2  in
                           let uu____21828 =
                             let uu____21831 =
                               let uu____21832 =
                                 let uu____21848 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____21848)  in
                               FStar_Syntax_Syntax.NT uu____21832  in
                             uu____21831 :: (env2.subst)  in
                           {
                             tcenv = (uu___803_21713.tcenv);
                             subst = uu____21828;
                             tc_const = (uu___803_21713.tc_const)
                           }  in
                         let uu____21870 =
                           let uu____21873 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____21874 =
                             let uu____21877 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____21877 :: acc  in
                           uu____21873 :: uu____21874  in
                         (env3, uu____21870)
                       else
                         (let x =
                            let uu___806_21950 = bv  in
                            let uu____21961 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___806_21950.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___806_21950.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____21961
                            }  in
                          let uu____21972 =
                            let uu____21975 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____21975 :: acc  in
                          (env2, uu____21972))) (env1, []) binders1
             in
          (match uu____20885 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____22231 =
                 let check_what =
                   let uu____22342 = is_monadic rc_opt1  in
                   if uu____22342 then check_m else check_n  in
                 let uu____22432 = check_what env2 body1  in
                 match uu____22432 with
                 | (t,s_body,u_body) ->
                     let uu____22500 =
                       let uu____22511 =
                         let uu____22512 = is_monadic rc_opt1  in
                         if uu____22512 then M t else N t  in
                       comp_of_nm uu____22511  in
                     (uu____22500, s_body, u_body)
                  in
               (match uu____22231 with
                | (comp,s_body,u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp  in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None  ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None  ->
                               let rc1 =
                                 let uu____22671 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___6_22677  ->
                                           match uu___6_22677 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____22680 -> false))
                                    in
                                 if uu____22671
                                 then
                                   let uu____22690 =
                                     FStar_List.filter
                                       (fun uu___7_22694  ->
                                          match uu___7_22694 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____22697 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____22690
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____22727 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___8_22733  ->
                                         match uu___8_22733 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____22736 -> false))
                                  in
                               if uu____22727
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___9_22752  ->
                                        match uu___9_22752 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____22755 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____22757 =
                                   let uu____22772 =
                                     let uu____22781 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____22781
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____22772 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____22757
                               else
                                 (let uu____22807 =
                                    let uu___847_22822 = rc  in
                                    let uu____22837 =
                                      let uu____22846 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____22846
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___847_22822.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____22837;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___847_22822.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____22807))
                       in
                    let uu____22870 =
                      let comp1 =
                        let uu____22897 = is_monadic rc_opt1  in
                        let uu____22899 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____22897 uu____22899
                         in
                      let uu____22908 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____22908,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____22870 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____23042 =
                             let uu____23043 =
                               let uu____23078 =
                                 let uu____23088 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____23088 s_rc_opt  in
                               (s_binders1, s_body1, uu____23078)  in
                             FStar_Syntax_Syntax.Tm_abs uu____23043  in
                           mk1 uu____23042  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____23140 =
                             let uu____23141 =
                               let uu____23176 =
                                 let uu____23186 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____23186 u_rc_opt  in
                               (u_binders2, u_body2, uu____23176)  in
                             FStar_Syntax_Syntax.Tm_abs uu____23141  in
                           mk1 uu____23140  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____23226;_};
            FStar_Syntax_Syntax.fv_delta = uu____23227;
            FStar_Syntax_Syntax.fv_qual = uu____23228;_}
          ->
          let uu____23239 =
            let uu____23248 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____23248  in
          (match uu____23239 with
           | (uu____23303,t) ->
               let uu____23313 =
                 let uu____23314 = normalize1 t  in N uu____23314  in
               (uu____23313, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____23331;
             FStar_Syntax_Syntax.vars = uu____23332;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____23451 = FStar_Syntax_Util.head_and_args e  in
          (match uu____23451 with
           | (unary_op1,uu____23491) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____23618;
             FStar_Syntax_Syntax.vars = uu____23619;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____23763 = FStar_Syntax_Util.head_and_args e  in
          (match uu____23763 with
           | (unary_op1,uu____23803) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____23942;
             FStar_Syntax_Syntax.vars = uu____23943;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____24009 = infer env a  in
          (match uu____24009 with
           | (t,s,u) ->
               let uu____24057 = FStar_Syntax_Util.head_and_args e  in
               (match uu____24057 with
                | (head1,uu____24097) ->
                    let uu____24138 =
                      let uu____24139 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____24139  in
                    let uu____24148 =
                      let uu____24157 =
                        let uu____24158 =
                          let uu____24183 =
                            let uu____24198 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____24198]  in
                          (head1, uu____24183)  in
                        FStar_Syntax_Syntax.Tm_app uu____24158  in
                      mk1 uu____24157  in
                    let uu____24255 =
                      let uu____24264 =
                        let uu____24265 =
                          let uu____24290 =
                            let uu____24305 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____24305]  in
                          (head1, uu____24290)  in
                        FStar_Syntax_Syntax.Tm_app uu____24265  in
                      mk1 uu____24264  in
                    (uu____24138, uu____24148, uu____24255)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____24370;
             FStar_Syntax_Syntax.vars = uu____24371;_},(a1,uu____24373)::a2::[])
          ->
          let uu____24465 = infer env a1  in
          (match uu____24465 with
           | (t,s,u) ->
               let uu____24513 = FStar_Syntax_Util.head_and_args e  in
               (match uu____24513 with
                | (head1,uu____24553) ->
                    let uu____24594 =
                      let uu____24603 =
                        let uu____24604 =
                          let uu____24629 =
                            let uu____24644 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____24644; a2]  in
                          (head1, uu____24629)  in
                        FStar_Syntax_Syntax.Tm_app uu____24604  in
                      mk1 uu____24603  in
                    let uu____24713 =
                      let uu____24722 =
                        let uu____24723 =
                          let uu____24748 =
                            let uu____24763 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____24763; a2]  in
                          (head1, uu____24748)  in
                        FStar_Syntax_Syntax.Tm_app uu____24723  in
                      mk1 uu____24722  in
                    (t, uu____24594, uu____24713)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____24840;
             FStar_Syntax_Syntax.vars = uu____24841;_},uu____24842)
          ->
          let uu____24883 =
            let uu____24889 =
              let uu____24891 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____24891
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____24889)  in
          FStar_Errors.raise_error uu____24883 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____24909;
             FStar_Syntax_Syntax.vars = uu____24910;_},uu____24911)
          ->
          let uu____24952 =
            let uu____24958 =
              let uu____24960 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____24960
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____24958)  in
          FStar_Errors.raise_error uu____24952 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____25020 = check_n env head1  in
          (match uu____25020 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____25095 =
                   let uu____25096 = FStar_Syntax_Subst.compress t  in
                   uu____25096.FStar_Syntax_Syntax.n  in
                 match uu____25095 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____25108 -> true
                 | uu____25133 -> false  in
               let rec flatten1 t =
                 let uu____25172 =
                   let uu____25173 = FStar_Syntax_Subst.compress t  in
                   uu____25173.FStar_Syntax_Syntax.n  in
                 match uu____25172 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____25209);
                                FStar_Syntax_Syntax.pos = uu____25210;
                                FStar_Syntax_Syntax.vars = uu____25211;_})
                     when is_arrow t1 ->
                     let uu____25266 = flatten1 t1  in
                     (match uu____25266 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____25443,uu____25444) -> flatten1 e1
                 | uu____25525 ->
                     let uu____25526 =
                       let uu____25532 =
                         let uu____25534 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____25534
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____25532)  in
                     FStar_Errors.raise_err uu____25526
                  in
               let uu____25561 = flatten1 t_head  in
               (match uu____25561 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____25689 =
                          let uu____25695 =
                            let uu____25697 = FStar_Util.string_of_int n1  in
                            let uu____25699 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____25701 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____25697 uu____25699 uu____25701
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____25695)
                           in
                        FStar_Errors.raise_err uu____25689)
                     else ();
                     (let uu____25707 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____25707 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____25793 args1 =
                            match uu____25793 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____25951 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____25951
                                 | (binders3,[]) ->
                                     let uu____26015 =
                                       let uu____26016 =
                                         let uu____26027 =
                                           let uu____26036 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____26036
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____26027
                                          in
                                       uu____26016.FStar_Syntax_Syntax.n  in
                                     (match uu____26015 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____26104 =
                                            let uu____26113 =
                                              let uu____26114 =
                                                let uu____26138 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____26138)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____26114
                                               in
                                            mk1 uu____26113  in
                                          N uu____26104
                                      | uu____26168 -> failwith "wat?")
                                 | ([],uu____26170::uu____26171) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____26250)::binders3,(arg,uu____26253)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____26412 = FStar_List.splitAt n' binders1
                             in
                          (match uu____26412 with
                           | (binders2,uu____26469) ->
                               let uu____26522 =
                                 let uu____26553 =
                                   FStar_List.map2
                                     (fun uu____26640  ->
                                        fun uu____26641  ->
                                          match (uu____26640, uu____26641)
                                          with
                                          | ((bv,uu____26715),(arg,q)) ->
                                              let uu____26771 =
                                                let uu____26772 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____26772.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____26771 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____26809 ->
                                                   let uu____26810 =
                                                     let uu____26821 =
                                                       star_type' env arg  in
                                                     (uu____26821, q)  in
                                                   (uu____26810, [(arg, q)])
                                               | uu____26890 ->
                                                   let uu____26891 =
                                                     check_n env arg  in
                                                   (match uu____26891 with
                                                    | (uu____26936,s_arg,u_arg)
                                                        ->
                                                        let uu____26963 =
                                                          let uu____26976 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____26976
                                                          then
                                                            let uu____26991 =
                                                              let uu____27002
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____27002,
                                                                q)
                                                               in
                                                            [uu____26991;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____26963))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____26553  in
                               (match uu____26522 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____27222 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____27251 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____27222, uu____27251)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____27417) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____27431) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____27445,uu____27446) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____27528 =
            let uu____27529 = env.tc_const c  in N uu____27529  in
          (uu____27528, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____27572 ->
          let uu____27597 =
            let uu____27599 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____27599  in
          failwith uu____27597
      | FStar_Syntax_Syntax.Tm_type uu____27616 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____27632 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____27671 ->
          let uu____27687 =
            let uu____27689 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____27689  in
          failwith uu____27687
      | FStar_Syntax_Syntax.Tm_uvar uu____27706 ->
          let uu____27727 =
            let uu____27729 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____27729  in
          failwith uu____27727
      | FStar_Syntax_Syntax.Tm_delayed uu____27746 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____27792 =
            let uu____27794 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____27794  in
          failwith uu____27792

and (mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
          -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____27993 = check_n env e0  in
          match uu____27993 with
          | (uu____28026,s_e0,u_e0) ->
              let uu____28053 =
                let uu____28101 =
                  FStar_List.map
                    (fun b  ->
                       let uu____28200 = FStar_Syntax_Subst.open_branch b  in
                       match uu____28200 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1122_28397 = env  in
                             let uu____28512 =
                               let uu____28621 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____28621
                                in
                             {
                               tcenv = uu____28512;
                               subst = (uu___1122_28397.subst);
                               tc_const = (uu___1122_28397.tc_const)
                             }  in
                           let uu____28688 = f env1 body  in
                           (match uu____28688 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____28857 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____28101  in
              (match uu____28053 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____29055 = FStar_List.hd nms  in
                     match uu____29055 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___10_29076  ->
                          match uu___10_29076 with
                          | M uu____29078 -> true
                          | uu____29084 -> false) nms
                      in
                   let uu____29086 =
                     let uu____29145 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____29298  ->
                              match uu____29298 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____29692 =
                                         check env original_body (M t2)  in
                                       (match uu____29692 with
                                        | (uu____29759,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____29858,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____29145  in
                   (match uu____29086 with
                    | (nms1,s_branches,u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk1 env t1  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu____30206  ->
                                 match uu____30206 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____30306 =
                                         let uu____30307 =
                                           let uu____30332 =
                                             let uu____30347 =
                                               let uu____30360 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____30371 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____30360, uu____30371)  in
                                             [uu____30347]  in
                                           (s_body, uu____30332)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____30307
                                          in
                                       mk1 uu____30306  in
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
                            let uu____30611 =
                              let uu____30612 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____30612]  in
                            let uu____30646 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____30611 uu____30646
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____30708 =
                              let uu____30722 =
                                let uu____30734 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____30734
                                 in
                              [uu____30722]  in
                            let uu____30783 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____30708 uu____30783
                             in
                          let uu____30794 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____30889 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____30794, uu____30889)
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
                           let uu____31104 =
                             let uu____31113 =
                               let uu____31114 =
                                 let uu____31161 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____31161,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____31114
                                in
                             mk1 uu____31113  in
                           let uu____31291 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____31104, uu____31291))))

and (mk_let :
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
            -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun binding  ->
      fun e2  ->
        fun proceed  ->
          fun ensure_m  ->
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                e2.FStar_Syntax_Syntax.pos
               in
            let e1 = binding.FStar_Syntax_Syntax.lbdef  in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname  in
            let x_binders =
              let uu____31632 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____31632]  in
            let uu____31666 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____31666 with
            | (x_binders1,e21) ->
                let uu____31699 = infer env e1  in
                (match uu____31699 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____31766 = is_C t1  in
                       if uu____31766
                       then
                         let uu___1208_31776 = binding  in
                         let uu____31791 =
                           let uu____31802 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____31802  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1208_31776.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1208_31776.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____31791;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1208_31776.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1208_31776.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1208_31776.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1208_31776.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1211_31928 = env  in
                       let uu____32043 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1213_32153 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1213_32153.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1213_32153.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____32043;
                         subst = (uu___1211_31928.subst);
                         tc_const = (uu___1211_31928.tc_const)
                       }  in
                     let uu____32164 = proceed env1 e21  in
                     (match uu____32164 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1220_32227 = binding  in
                            let uu____32242 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1220_32227.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1220_32227.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____32242;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1220_32227.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1220_32227.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1220_32227.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1220_32227.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____32253 =
                            let uu____32262 =
                              let uu____32263 =
                                let uu____32288 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1223_32338 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1223_32338.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1223_32338.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1223_32338.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1223_32338.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1223_32338.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1223_32338.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____32288)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____32263  in
                            mk1 uu____32262  in
                          let uu____32360 =
                            let uu____32369 =
                              let uu____32370 =
                                let uu____32395 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1225_32445 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1225_32445.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1225_32445.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1225_32445.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1225_32445.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1225_32445.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1225_32445.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____32395)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____32370  in
                            mk1 uu____32369  in
                          (nm_rec, uu____32253, uu____32360))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1232_32513 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1232_32513.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1232_32513.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1232_32513.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1232_32513.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1232_32513.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1235_32643 = env  in
                       let uu____32758 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1237_32868 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1237_32868.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1237_32868.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____32758;
                         subst = (uu___1235_32643.subst);
                         tc_const = (uu___1235_32643.tc_const)
                       }  in
                     let uu____32879 = ensure_m env1 e21  in
                     (match uu____32879 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____32973 =
                              let uu____32974 =
                                let uu____32999 =
                                  let uu____33014 =
                                    let uu____33027 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____33038 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____33027, uu____33038)  in
                                  [uu____33014]  in
                                (s_e2, uu____32999)  in
                              FStar_Syntax_Syntax.Tm_app uu____32974  in
                            mk1 uu____32973  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____33123 =
                              let uu____33124 =
                                let uu____33149 =
                                  let uu____33164 =
                                    let uu____33177 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____33177)  in
                                  [uu____33164]  in
                                (s_e1, uu____33149)  in
                              FStar_Syntax_Syntax.Tm_app uu____33124  in
                            mk1 uu____33123  in
                          let uu____33233 =
                            let uu____33242 =
                              let uu____33243 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____33243]  in
                            FStar_Syntax_Util.abs uu____33242 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____33284 =
                            let uu____33293 =
                              let uu____33294 =
                                let uu____33319 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1249_33369 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1249_33369.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1249_33369.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1249_33369.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1249_33369.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1249_33369.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1249_33369.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____33319)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____33294  in
                            mk1 uu____33293  in
                          ((M t2), uu____33233, uu____33284)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____33481 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____33481  in
      let uu____33490 = check env e mn  in
      match uu____33490 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____33558 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____33674 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____33674  in
      let uu____33683 = check env e mn  in
      match uu____33683 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____33751 -> failwith "[check_m]: impossible"

and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and (mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp) =
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

and (type_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun t  -> FStar_Syntax_Util.comp_result t

and (trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____33901 =
           let uu____33903 = is_C c  in Prims.op_Negation uu____33903  in
         if uu____33901 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____33921 =
           let uu____33922 = FStar_Syntax_Subst.compress c  in
           uu____33922.FStar_Syntax_Syntax.n  in
         match uu____33921 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____33979 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____33979 with
              | (wp_head,wp_args) ->
                  ((let uu____34051 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____34078 =
                           let uu____34080 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____34080
                            in
                         Prims.op_Negation uu____34078)
                       in
                    if uu____34051 then failwith "mismatch" else ());
                   (let uu____34105 =
                      let uu____34106 =
                        let uu____34131 =
                          FStar_List.map2
                            (fun uu____34185  ->
                               fun uu____34186  ->
                                 match (uu____34185, uu____34186) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____34292 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____34292
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____34301 =
                                         let uu____34303 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____34303 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____34301
                                       then
                                         let uu____34305 =
                                           let uu____34311 =
                                             let uu____34313 =
                                               print_implicit q  in
                                             let uu____34315 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____34313 uu____34315
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____34311)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____34305
                                       else ());
                                      (let uu____34321 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____34321, q)))) args wp_args
                           in
                        (head1, uu____34131)  in
                      FStar_Syntax_Syntax.Tm_app uu____34106  in
                    mk1 uu____34105)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____34410 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____34410 with
              | (binders_orig,comp1) ->
                  let uu____34433 =
                    let uu____34460 =
                      FStar_List.map
                        (fun uu____34525  ->
                           match uu____34525 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____34586 = is_C h  in
                               if uu____34586
                               then
                                 let w' =
                                   let uu____34622 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____34622
                                    in
                                 let uu____34632 =
                                   let uu____34646 =
                                     let uu____34660 =
                                       let uu____34672 =
                                         let uu____34683 =
                                           let uu____34692 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____34692  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____34683
                                          in
                                       (uu____34672, q)  in
                                     [uu____34660]  in
                                   (w', q) :: uu____34646  in
                                 (w', uu____34632)
                               else
                                 (let x =
                                    let uu____34779 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____34779
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____34460  in
                  (match uu____34433 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____34938 =
                           let uu____34941 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____34941
                            in
                         FStar_Syntax_Subst.subst_comp uu____34938 comp1  in
                       let app =
                         let uu____34953 =
                           let uu____34954 =
                             let uu____34979 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____35016 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____35025 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____35016, uu____35025)) bvs
                                in
                             (wp, uu____34979)  in
                           FStar_Syntax_Syntax.Tm_app uu____34954  in
                         mk1 uu____34953  in
                       let comp3 =
                         let uu____35060 = type_of_comp comp2  in
                         let uu____35069 = is_monadic_comp comp2  in
                         trans_G env uu____35060 uu____35069 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____35072,uu____35073) ->
             trans_F_ env e wp
         | uu____35154 -> failwith "impossible trans_F_")

and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____35235 =
              let uu____35246 = star_type' env h  in
              let uu____35257 =
                let uu____35272 =
                  let uu____35285 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____35285)  in
                [uu____35272]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____35246;
                FStar_Syntax_Syntax.effect_args = uu____35257;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____35235
          else
            (let uu____35323 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____35323)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
    FStar_TypeChecker_Env.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____35540 = n env.tcenv t  in star_type' env uu____35540
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____35702 = n env.tcenv t  in check_n env uu____35702
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____35865 = n env.tcenv c  in
        let uu____35874 = n env.tcenv wp  in
        trans_F_ env uu____35865 uu____35874
  