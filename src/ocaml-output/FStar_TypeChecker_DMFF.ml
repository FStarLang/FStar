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
              let uu___613_61008 = a  in
              let uu____61009 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_61008.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_61008.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____61009
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____61022 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____61022
             then
               (d "Elaborating extra WP combinators";
                (let uu____61028 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____61028))
             else ());
            (let rec collect_binders t =
               let uu____61047 =
                 let uu____61048 =
                   let uu____61051 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____61051
                    in
                 uu____61048.FStar_Syntax_Syntax.n  in
               match uu____61047 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____61086) -> t1
                     | uu____61095 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____61097 = collect_binders rest  in
                   FStar_List.append bs uu____61097
               | FStar_Syntax_Syntax.Tm_type uu____61112 -> []
               | uu____61119 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____61146 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____61146
                 FStar_Syntax_Util.name_binders
                in
             (let uu____61172 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____61172
              then
                let uu____61176 =
                  let uu____61178 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____61178  in
                d uu____61176
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____61216 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____61216 with
                | (sigelt,fv) ->
                    ((let uu____61224 =
                        let uu____61227 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____61227
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____61224);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____61307  ->
                     match uu____61307 with
                     | (t,b) ->
                         let uu____61321 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____61321))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____61360 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____61360))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____61394 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____61394)
                 in
              let uu____61397 =
                let uu____61414 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____61439 =
                        let uu____61442 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____61442  in
                      FStar_Syntax_Util.arrow gamma uu____61439  in
                    let uu____61443 =
                      let uu____61444 =
                        let uu____61453 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____61460 =
                          let uu____61469 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____61469]  in
                        uu____61453 :: uu____61460  in
                      FStar_List.append binders uu____61444  in
                    FStar_Syntax_Util.abs uu____61443 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____61500 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____61501 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____61500, uu____61501)  in
                match uu____61414 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____61543 =
                        let uu____61544 =
                          let uu____61561 =
                            let uu____61572 =
                              FStar_List.map
                                (fun uu____61594  ->
                                   match uu____61594 with
                                   | (bv,uu____61606) ->
                                       let uu____61611 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____61612 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____61611, uu____61612)) binders
                               in
                            let uu____61614 =
                              let uu____61621 =
                                let uu____61626 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____61627 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____61626, uu____61627)  in
                              let uu____61629 =
                                let uu____61636 =
                                  let uu____61641 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____61641)  in
                                [uu____61636]  in
                              uu____61621 :: uu____61629  in
                            FStar_List.append uu____61572 uu____61614  in
                          (fv, uu____61561)  in
                        FStar_Syntax_Syntax.Tm_app uu____61544  in
                      mk1 uu____61543  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____61397 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____61714 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____61714
                       in
                    let ret1 =
                      let uu____61719 =
                        let uu____61720 =
                          let uu____61723 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____61723  in
                        FStar_Syntax_Util.residual_tot uu____61720  in
                      FStar_Pervasives_Native.Some uu____61719  in
                    let body =
                      let uu____61727 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____61727 ret1  in
                    let uu____61730 =
                      let uu____61731 = mk_all_implicit binders  in
                      let uu____61738 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____61731 uu____61738  in
                    FStar_Syntax_Util.abs uu____61730 body ret1  in
                  let c_pure1 =
                    let uu____61776 = mk_lid "pure"  in
                    register env1 uu____61776 c_pure  in
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
                      let uu____61786 =
                        let uu____61787 =
                          let uu____61788 =
                            let uu____61797 =
                              let uu____61804 =
                                let uu____61805 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____61805
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____61804  in
                            [uu____61797]  in
                          let uu____61818 =
                            let uu____61821 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____61821  in
                          FStar_Syntax_Util.arrow uu____61788 uu____61818  in
                        mk_gctx uu____61787  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____61786
                       in
                    let r =
                      let uu____61824 =
                        let uu____61825 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____61825  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____61824
                       in
                    let ret1 =
                      let uu____61830 =
                        let uu____61831 =
                          let uu____61834 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____61834  in
                        FStar_Syntax_Util.residual_tot uu____61831  in
                      FStar_Pervasives_Native.Some uu____61830  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____61844 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____61847 =
                          let uu____61858 =
                            let uu____61861 =
                              let uu____61862 =
                                let uu____61863 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____61863
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____61862  in
                            [uu____61861]  in
                          FStar_List.append gamma_as_args uu____61858  in
                        FStar_Syntax_Util.mk_app uu____61844 uu____61847  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____61866 =
                      let uu____61867 = mk_all_implicit binders  in
                      let uu____61874 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____61867 uu____61874  in
                    FStar_Syntax_Util.abs uu____61866 outer_body ret1  in
                  let c_app1 =
                    let uu____61926 = mk_lid "app"  in
                    register env1 uu____61926 c_app  in
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
                      let uu____61938 =
                        let uu____61947 =
                          let uu____61954 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____61954  in
                        [uu____61947]  in
                      let uu____61967 =
                        let uu____61970 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____61970  in
                      FStar_Syntax_Util.arrow uu____61938 uu____61967  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____61974 =
                        let uu____61975 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____61975  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____61974
                       in
                    let ret1 =
                      let uu____61980 =
                        let uu____61981 =
                          let uu____61984 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____61984  in
                        FStar_Syntax_Util.residual_tot uu____61981  in
                      FStar_Pervasives_Native.Some uu____61980  in
                    let uu____61985 =
                      let uu____61986 = mk_all_implicit binders  in
                      let uu____61993 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____61986 uu____61993  in
                    let uu____62044 =
                      let uu____62047 =
                        let uu____62058 =
                          let uu____62061 =
                            let uu____62062 =
                              let uu____62073 =
                                let uu____62076 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____62076]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62073
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62062  in
                          let uu____62085 =
                            let uu____62088 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____62088]  in
                          uu____62061 :: uu____62085  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62058
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62047  in
                    FStar_Syntax_Util.abs uu____61985 uu____62044 ret1  in
                  let c_lift11 =
                    let uu____62098 = mk_lid "lift1"  in
                    register env1 uu____62098 c_lift1  in
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
                      let uu____62112 =
                        let uu____62121 =
                          let uu____62128 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62128  in
                        let uu____62129 =
                          let uu____62138 =
                            let uu____62145 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____62145  in
                          [uu____62138]  in
                        uu____62121 :: uu____62129  in
                      let uu____62164 =
                        let uu____62167 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62167  in
                      FStar_Syntax_Util.arrow uu____62112 uu____62164  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62171 =
                        let uu____62172 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62172  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62171
                       in
                    let a2 =
                      let uu____62175 =
                        let uu____62176 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____62176  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____62175
                       in
                    let ret1 =
                      let uu____62181 =
                        let uu____62182 =
                          let uu____62185 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____62185  in
                        FStar_Syntax_Util.residual_tot uu____62182  in
                      FStar_Pervasives_Native.Some uu____62181  in
                    let uu____62186 =
                      let uu____62187 = mk_all_implicit binders  in
                      let uu____62194 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____62187 uu____62194  in
                    let uu____62259 =
                      let uu____62262 =
                        let uu____62273 =
                          let uu____62276 =
                            let uu____62277 =
                              let uu____62288 =
                                let uu____62291 =
                                  let uu____62292 =
                                    let uu____62303 =
                                      let uu____62306 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____62306]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____62303
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____62292
                                   in
                                let uu____62315 =
                                  let uu____62318 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____62318]  in
                                uu____62291 :: uu____62315  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62288
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____62277  in
                          let uu____62327 =
                            let uu____62330 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____62330]  in
                          uu____62276 :: uu____62327  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62273
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62262  in
                    FStar_Syntax_Util.abs uu____62186 uu____62259 ret1  in
                  let c_lift21 =
                    let uu____62340 = mk_lid "lift2"  in
                    register env1 uu____62340 c_lift2  in
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
                      let uu____62352 =
                        let uu____62361 =
                          let uu____62368 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62368  in
                        [uu____62361]  in
                      let uu____62381 =
                        let uu____62384 =
                          let uu____62385 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62385  in
                        FStar_Syntax_Syntax.mk_Total uu____62384  in
                      FStar_Syntax_Util.arrow uu____62352 uu____62381  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____62391 =
                        let uu____62392 =
                          let uu____62395 =
                            let uu____62396 =
                              let uu____62405 =
                                let uu____62412 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____62412
                                 in
                              [uu____62405]  in
                            let uu____62425 =
                              let uu____62428 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____62428  in
                            FStar_Syntax_Util.arrow uu____62396 uu____62425
                             in
                          mk_ctx uu____62395  in
                        FStar_Syntax_Util.residual_tot uu____62392  in
                      FStar_Pervasives_Native.Some uu____62391  in
                    let e1 =
                      let uu____62430 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____62430
                       in
                    let body =
                      let uu____62435 =
                        let uu____62436 =
                          let uu____62445 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____62445]  in
                        FStar_List.append gamma uu____62436  in
                      let uu____62470 =
                        let uu____62473 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____62476 =
                          let uu____62487 =
                            let uu____62488 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____62488  in
                          let uu____62489 = args_of_binders1 gamma  in
                          uu____62487 :: uu____62489  in
                        FStar_Syntax_Util.mk_app uu____62473 uu____62476  in
                      FStar_Syntax_Util.abs uu____62435 uu____62470 ret1  in
                    let uu____62492 =
                      let uu____62493 = mk_all_implicit binders  in
                      let uu____62500 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____62493 uu____62500  in
                    FStar_Syntax_Util.abs uu____62492 body ret1  in
                  let c_push1 =
                    let uu____62545 = mk_lid "push"  in
                    register env1 uu____62545 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____62572 =
                        let uu____62573 =
                          let uu____62590 = args_of_binders1 binders  in
                          (c, uu____62590)  in
                        FStar_Syntax_Syntax.Tm_app uu____62573  in
                      mk1 uu____62572
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____62619 =
                        let uu____62620 =
                          let uu____62629 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____62636 =
                            let uu____62645 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____62645]  in
                          uu____62629 :: uu____62636  in
                        let uu____62670 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____62620 uu____62670  in
                      FStar_Syntax_Syntax.mk_Total uu____62619  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____62675 =
                      let uu____62676 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____62676  in
                    let uu____62691 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____62696 =
                        let uu____62699 =
                          let uu____62710 =
                            let uu____62713 =
                              let uu____62714 =
                                let uu____62725 =
                                  let uu____62734 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____62734  in
                                [uu____62725]  in
                              FStar_Syntax_Util.mk_app l_ite uu____62714  in
                            [uu____62713]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____62710
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____62699  in
                      FStar_Syntax_Util.ascribe uu____62696
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____62675 uu____62691
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____62778 = mk_lid "wp_if_then_else"  in
                    register env1 uu____62778 wp_if_then_else  in
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
                      let uu____62795 =
                        let uu____62806 =
                          let uu____62809 =
                            let uu____62810 =
                              let uu____62821 =
                                let uu____62824 =
                                  let uu____62825 =
                                    let uu____62836 =
                                      let uu____62845 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62845
                                       in
                                    [uu____62836]  in
                                  FStar_Syntax_Util.mk_app l_and uu____62825
                                   in
                                [uu____62824]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62821
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62810  in
                          let uu____62870 =
                            let uu____62873 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____62873]  in
                          uu____62809 :: uu____62870  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62806
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62795  in
                    let uu____62882 =
                      let uu____62883 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____62883  in
                    FStar_Syntax_Util.abs uu____62882 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____62899 = mk_lid "wp_assert"  in
                    register env1 uu____62899 wp_assert  in
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
                      let uu____62916 =
                        let uu____62927 =
                          let uu____62930 =
                            let uu____62931 =
                              let uu____62942 =
                                let uu____62945 =
                                  let uu____62946 =
                                    let uu____62957 =
                                      let uu____62966 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62966
                                       in
                                    [uu____62957]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____62946
                                   in
                                [uu____62945]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62942
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62931  in
                          let uu____62991 =
                            let uu____62994 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____62994]  in
                          uu____62930 :: uu____62991  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62927
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62916  in
                    let uu____63003 =
                      let uu____63004 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____63004  in
                    FStar_Syntax_Util.abs uu____63003 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____63020 = mk_lid "wp_assume"  in
                    register env1 uu____63020 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____63033 =
                        let uu____63042 =
                          let uu____63049 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____63049  in
                        [uu____63042]  in
                      let uu____63062 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____63033 uu____63062  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____63070 =
                        let uu____63081 =
                          let uu____63084 =
                            let uu____63085 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____63085  in
                          let uu____63104 =
                            let uu____63107 =
                              let uu____63108 =
                                let uu____63119 =
                                  let uu____63122 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____63122]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____63119
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____63108
                               in
                            [uu____63107]  in
                          uu____63084 :: uu____63104  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63081
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63070  in
                    let uu____63139 =
                      let uu____63140 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____63140  in
                    FStar_Syntax_Util.abs uu____63139 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____63156 = mk_lid "wp_close"  in
                    register env1 uu____63156 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____63167 =
                      let uu____63168 =
                        let uu____63169 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____63169
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____63168
                       in
                    FStar_Pervasives_Native.Some uu____63167  in
                  let mk_forall1 x body =
                    let uu____63181 =
                      let uu____63188 =
                        let uu____63189 =
                          let uu____63206 =
                            let uu____63217 =
                              let uu____63226 =
                                let uu____63227 =
                                  let uu____63228 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____63228]  in
                                FStar_Syntax_Util.abs uu____63227 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____63226  in
                            [uu____63217]  in
                          (FStar_Syntax_Util.tforall, uu____63206)  in
                        FStar_Syntax_Syntax.Tm_app uu____63189  in
                      FStar_Syntax_Syntax.mk uu____63188  in
                    uu____63181 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____63286 =
                      let uu____63287 = FStar_Syntax_Subst.compress t  in
                      uu____63287.FStar_Syntax_Syntax.n  in
                    match uu____63286 with
                    | FStar_Syntax_Syntax.Tm_type uu____63291 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63324  ->
                              match uu____63324 with
                              | (b,uu____63333) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____63338 -> true  in
                  let rec is_monotonic t =
                    let uu____63351 =
                      let uu____63352 = FStar_Syntax_Subst.compress t  in
                      uu____63352.FStar_Syntax_Syntax.n  in
                    match uu____63351 with
                    | FStar_Syntax_Syntax.Tm_type uu____63356 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63389  ->
                              match uu____63389 with
                              | (b,uu____63398) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____63403 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____63477 =
                      let uu____63478 = FStar_Syntax_Subst.compress t1  in
                      uu____63478.FStar_Syntax_Syntax.n  in
                    match uu____63477 with
                    | FStar_Syntax_Syntax.Tm_type uu____63483 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____63486);
                                      FStar_Syntax_Syntax.pos = uu____63487;
                                      FStar_Syntax_Syntax.vars = uu____63488;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63532 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63532
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63542 =
                              let uu____63545 =
                                let uu____63556 =
                                  let uu____63565 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63565  in
                                [uu____63556]  in
                              FStar_Syntax_Util.mk_app x uu____63545  in
                            let uu____63582 =
                              let uu____63585 =
                                let uu____63596 =
                                  let uu____63605 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63605  in
                                [uu____63596]  in
                              FStar_Syntax_Util.mk_app y uu____63585  in
                            mk_rel1 b uu____63542 uu____63582  in
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
                             let uu____63629 =
                               let uu____63632 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63635 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63632 uu____63635  in
                             let uu____63638 =
                               let uu____63641 =
                                 let uu____63644 =
                                   let uu____63655 =
                                     let uu____63664 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63664
                                      in
                                   [uu____63655]  in
                                 FStar_Syntax_Util.mk_app x uu____63644  in
                               let uu____63681 =
                                 let uu____63684 =
                                   let uu____63695 =
                                     let uu____63704 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63704
                                      in
                                   [uu____63695]  in
                                 FStar_Syntax_Util.mk_app y uu____63684  in
                               mk_rel1 b uu____63641 uu____63681  in
                             FStar_Syntax_Util.mk_imp uu____63629 uu____63638
                              in
                           let uu____63721 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63721)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____63724);
                                      FStar_Syntax_Syntax.pos = uu____63725;
                                      FStar_Syntax_Syntax.vars = uu____63726;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63770 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63770
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63780 =
                              let uu____63783 =
                                let uu____63794 =
                                  let uu____63803 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63803  in
                                [uu____63794]  in
                              FStar_Syntax_Util.mk_app x uu____63783  in
                            let uu____63820 =
                              let uu____63823 =
                                let uu____63834 =
                                  let uu____63843 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63843  in
                                [uu____63834]  in
                              FStar_Syntax_Util.mk_app y uu____63823  in
                            mk_rel1 b uu____63780 uu____63820  in
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
                             let uu____63867 =
                               let uu____63870 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63873 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63870 uu____63873  in
                             let uu____63876 =
                               let uu____63879 =
                                 let uu____63882 =
                                   let uu____63893 =
                                     let uu____63902 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63902
                                      in
                                   [uu____63893]  in
                                 FStar_Syntax_Util.mk_app x uu____63882  in
                               let uu____63919 =
                                 let uu____63922 =
                                   let uu____63933 =
                                     let uu____63942 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63942
                                      in
                                   [uu____63933]  in
                                 FStar_Syntax_Util.mk_app y uu____63922  in
                               mk_rel1 b uu____63879 uu____63919  in
                             FStar_Syntax_Util.mk_imp uu____63867 uu____63876
                              in
                           let uu____63959 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63959)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_63998 = t1  in
                          let uu____63999 =
                            let uu____64000 =
                              let uu____64015 =
                                let uu____64018 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____64018  in
                              ([binder], uu____64015)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____64000  in
                          {
                            FStar_Syntax_Syntax.n = uu____63999;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_63998.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_63998.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____64041 ->
                        failwith "unhandled arrow"
                    | uu____64059 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env1 t
                         in
                      let uu____64096 =
                        let uu____64097 = FStar_Syntax_Subst.compress t1  in
                        uu____64097.FStar_Syntax_Syntax.n  in
                      match uu____64096 with
                      | FStar_Syntax_Syntax.Tm_type uu____64100 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____64127 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____64127
                          ->
                          let project i tuple =
                            let projector =
                              let uu____64148 =
                                let uu____64149 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____64149 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____64148
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____64179 =
                            let uu____64190 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____64208  ->
                                     match uu____64208 with
                                     | (t2,q) ->
                                         let uu____64228 = project i x  in
                                         let uu____64231 = project i y  in
                                         mk_stronger t2 uu____64228
                                           uu____64231) args
                               in
                            match uu____64190 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____64179 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____64285);
                                      FStar_Syntax_Syntax.pos = uu____64286;
                                      FStar_Syntax_Syntax.vars = uu____64287;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64331  ->
                                   match uu____64331 with
                                   | (bv,q) ->
                                       let uu____64345 =
                                         let uu____64347 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64347  in
                                       FStar_Syntax_Syntax.gen_bv uu____64345
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64356 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64356) bvs
                             in
                          let body =
                            let uu____64358 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64361 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64358 uu____64361  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____64370);
                                      FStar_Syntax_Syntax.pos = uu____64371;
                                      FStar_Syntax_Syntax.vars = uu____64372;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64416  ->
                                   match uu____64416 with
                                   | (bv,q) ->
                                       let uu____64430 =
                                         let uu____64432 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64432  in
                                       FStar_Syntax_Syntax.gen_bv uu____64430
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64441 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64441) bvs
                             in
                          let body =
                            let uu____64443 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64446 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64443 uu____64446  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____64453 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____64456 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____64459 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____64462 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____64456 uu____64459 uu____64462  in
                    let uu____64465 =
                      let uu____64466 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____64466  in
                    FStar_Syntax_Util.abs uu____64465 body ret_tot_type  in
                  let stronger1 =
                    let uu____64508 = mk_lid "stronger"  in
                    register env1 uu____64508 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64516 = FStar_Util.prefix gamma  in
                    match uu____64516 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____64582 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____64582
                             in
                          let uu____64587 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____64587 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____64597 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____64597  in
                              let guard_free1 =
                                let uu____64609 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____64609  in
                              let pat =
                                let uu____64613 =
                                  let uu____64624 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____64624]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____64613
                                 in
                              let pattern_guarded_body =
                                let uu____64652 =
                                  let uu____64653 =
                                    let uu____64660 =
                                      let uu____64661 =
                                        let uu____64674 =
                                          let uu____64685 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____64685]  in
                                        [uu____64674]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____64661
                                       in
                                    (body, uu____64660)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____64653  in
                                mk1 uu____64652  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____64732 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____64741 =
                            let uu____64744 =
                              let uu____64745 =
                                let uu____64748 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____64751 =
                                  let uu____64762 = args_of_binders1 wp_args
                                     in
                                  let uu____64765 =
                                    let uu____64768 =
                                      let uu____64769 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____64769
                                       in
                                    [uu____64768]  in
                                  FStar_List.append uu____64762 uu____64765
                                   in
                                FStar_Syntax_Util.mk_app uu____64748
                                  uu____64751
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____64745  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____64744
                             in
                          FStar_Syntax_Util.abs gamma uu____64741
                            ret_gtot_type
                           in
                        let uu____64770 =
                          let uu____64771 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____64771  in
                        FStar_Syntax_Util.abs uu____64770 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____64787 = mk_lid "ite_wp"  in
                    register env1 uu____64787 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64795 = FStar_Util.prefix gamma  in
                    match uu____64795 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____64853 =
                            let uu____64854 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____64861 =
                              let uu____64872 =
                                let uu____64881 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____64881  in
                              [uu____64872]  in
                            FStar_Syntax_Util.mk_app uu____64854 uu____64861
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____64853
                           in
                        let uu____64898 =
                          let uu____64899 =
                            let uu____64908 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____64908 gamma  in
                          FStar_List.append binders uu____64899  in
                        FStar_Syntax_Util.abs uu____64898 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____64930 = mk_lid "null_wp"  in
                    register env1 uu____64930 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____64943 =
                        let uu____64954 =
                          let uu____64957 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____64958 =
                            let uu____64961 =
                              let uu____64962 =
                                let uu____64973 =
                                  let uu____64982 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____64982  in
                                [uu____64973]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____64962
                               in
                            let uu____64999 =
                              let uu____65002 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____65002]  in
                            uu____64961 :: uu____64999  in
                          uu____64957 :: uu____64958  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____64954
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____64943  in
                    let uu____65011 =
                      let uu____65012 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____65012  in
                    FStar_Syntax_Util.abs uu____65011 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____65028 = mk_lid "wp_trivial"  in
                    register env1 uu____65028 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____65034 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____65034
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____65046 =
                      let uu____65047 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____65047  in
                    let uu____65073 =
                      let uu___934_65074 = ed  in
                      let uu____65075 =
                        let uu____65076 = c wp_if_then_else2  in
                        ([], uu____65076)  in
                      let uu____65083 =
                        let uu____65084 = c ite_wp2  in ([], uu____65084)  in
                      let uu____65091 =
                        let uu____65092 = c stronger2  in ([], uu____65092)
                         in
                      let uu____65099 =
                        let uu____65100 = c wp_close2  in ([], uu____65100)
                         in
                      let uu____65107 =
                        let uu____65108 = c wp_assert2  in ([], uu____65108)
                         in
                      let uu____65115 =
                        let uu____65116 = c wp_assume2  in ([], uu____65116)
                         in
                      let uu____65123 =
                        let uu____65124 = c null_wp2  in ([], uu____65124)
                         in
                      let uu____65131 =
                        let uu____65132 = c wp_trivial2  in ([], uu____65132)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_65074.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_65074.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_65074.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_65074.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_65074.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_65074.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_65074.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____65075;
                        FStar_Syntax_Syntax.ite_wp = uu____65083;
                        FStar_Syntax_Syntax.stronger = uu____65091;
                        FStar_Syntax_Syntax.close_wp = uu____65099;
                        FStar_Syntax_Syntax.assert_p = uu____65107;
                        FStar_Syntax_Syntax.assume_p = uu____65115;
                        FStar_Syntax_Syntax.null_wp = uu____65123;
                        FStar_Syntax_Syntax.trivial = uu____65131;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_65074.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_65074.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_65074.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_65074.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_65074.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____65046, uu____65073)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_65156 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_65156.subst);
        tc_const = (uu___939_65156.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____65177 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____65196 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65216) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_65230  ->
                match uu___585_65230 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____65233 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____65235 ->
        let uu____65236 =
          let uu____65242 =
            let uu____65244 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____65244
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____65242)  in
        FStar_Errors.raise_error uu____65236 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_65254  ->
    match uu___586_65254 with
    | N t ->
        let uu____65257 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____65257
    | M t ->
        let uu____65261 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____65261
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____65270,c) -> nm_of_comp c
    | uu____65292 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____65305 = nm_of_comp c  in
    match uu____65305 with | M uu____65307 -> true | N uu____65309 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____65320 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____65336 =
        let uu____65345 =
          let uu____65352 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____65352  in
        [uu____65345]  in
      let uu____65371 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____65336 uu____65371  in
    let uu____65374 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____65374
  
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
        let uu____65416 =
          let uu____65417 =
            let uu____65432 =
              let uu____65441 =
                let uu____65448 =
                  let uu____65449 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____65449  in
                let uu____65450 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____65448, uu____65450)  in
              [uu____65441]  in
            let uu____65468 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____65432, uu____65468)  in
          FStar_Syntax_Syntax.Tm_arrow uu____65417  in
        mk1 uu____65416

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____65508) ->
          let binders1 =
            FStar_List.map
              (fun uu____65554  ->
                 match uu____65554 with
                 | (bv,aqual) ->
                     let uu____65573 =
                       let uu___989_65574 = bv  in
                       let uu____65575 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_65574.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_65574.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____65575
                       }  in
                     (uu____65573, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____65580,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____65582);
                              FStar_Syntax_Syntax.pos = uu____65583;
                              FStar_Syntax_Syntax.vars = uu____65584;_})
               ->
               let uu____65613 =
                 let uu____65614 =
                   let uu____65629 =
                     let uu____65632 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____65632  in
                   (binders1, uu____65629)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____65614  in
               mk1 uu____65613
           | uu____65643 ->
               let uu____65644 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____65644 with
                | N hn ->
                    let uu____65646 =
                      let uu____65647 =
                        let uu____65662 =
                          let uu____65665 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____65665  in
                        (binders1, uu____65662)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65647  in
                    mk1 uu____65646
                | M a ->
                    let uu____65677 =
                      let uu____65678 =
                        let uu____65693 =
                          let uu____65702 =
                            let uu____65711 =
                              let uu____65718 =
                                let uu____65719 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____65719  in
                              let uu____65720 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____65718, uu____65720)  in
                            [uu____65711]  in
                          FStar_List.append binders1 uu____65702  in
                        let uu____65744 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____65693, uu____65744)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65678  in
                    mk1 uu____65677))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____65838 = f x  in
                    FStar_Util.string_builder_append strb uu____65838);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____65847 = f x1  in
                         FStar_Util.string_builder_append strb uu____65847))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____65851 =
              let uu____65857 =
                let uu____65859 = FStar_Syntax_Print.term_to_string t2  in
                let uu____65861 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____65859 uu____65861
                 in
              (FStar_Errors.Warning_DependencyFound, uu____65857)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____65851  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____65883 =
              let uu____65884 = FStar_Syntax_Subst.compress ty  in
              uu____65884.FStar_Syntax_Syntax.n  in
            match uu____65883 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____65910 =
                  let uu____65912 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____65912  in
                if uu____65910
                then false
                else
                  (try
                     (fun uu___1038_65929  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____65953 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____65953 s  in
                              let uu____65956 =
                                let uu____65958 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____65958  in
                              if uu____65956
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____65964 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____65964 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____65989  ->
                                          match uu____65989 with
                                          | (bv,uu____66001) ->
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
            | uu____66029 ->
                ((let uu____66031 =
                    let uu____66037 =
                      let uu____66039 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____66039
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____66037)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____66031);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____66055 =
              let uu____66056 = FStar_Syntax_Subst.compress head2  in
              uu____66056.FStar_Syntax_Syntax.n  in
            match uu____66055 with
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
                  (let uu____66062 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____66062)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____66065 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____66065 with
                 | ((uu____66075,ty),uu____66077) ->
                     let uu____66082 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____66082
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____66095 =
                         let uu____66096 = FStar_Syntax_Subst.compress res
                            in
                         uu____66096.FStar_Syntax_Syntax.n  in
                       (match uu____66095 with
                        | FStar_Syntax_Syntax.Tm_app uu____66100 -> true
                        | uu____66118 ->
                            ((let uu____66120 =
                                let uu____66126 =
                                  let uu____66128 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____66128
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____66126)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____66120);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____66136 -> true
            | FStar_Syntax_Syntax.Tm_name uu____66138 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____66141) ->
                is_valid_application t2
            | uu____66146 -> false  in
          let uu____66148 = is_valid_application head1  in
          if uu____66148
          then
            let uu____66151 =
              let uu____66152 =
                let uu____66169 =
                  FStar_List.map
                    (fun uu____66198  ->
                       match uu____66198 with
                       | (t2,qual) ->
                           let uu____66223 = star_type' env t2  in
                           (uu____66223, qual)) args
                   in
                (head1, uu____66169)  in
              FStar_Syntax_Syntax.Tm_app uu____66152  in
            mk1 uu____66151
          else
            (let uu____66240 =
               let uu____66246 =
                 let uu____66248 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____66248
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____66246)  in
             FStar_Errors.raise_err uu____66240)
      | FStar_Syntax_Syntax.Tm_bvar uu____66252 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____66253 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____66254 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____66255 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____66283 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____66283 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_66291 = env  in
                 let uu____66292 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____66292;
                   subst = (uu___1110_66291.subst);
                   tc_const = (uu___1110_66291.tc_const)
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
               ((let uu___1125_66319 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_66319.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_66319.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____66326 =
            let uu____66327 =
              let uu____66334 = star_type' env t2  in (uu____66334, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____66327  in
          mk1 uu____66326
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____66386 =
            let uu____66387 =
              let uu____66414 = star_type' env e  in
              let uu____66417 =
                let uu____66434 =
                  let uu____66443 = star_type' env t2  in
                  FStar_Util.Inl uu____66443  in
                (uu____66434, FStar_Pervasives_Native.None)  in
              (uu____66414, uu____66417, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66387  in
          mk1 uu____66386
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____66531 =
            let uu____66532 =
              let uu____66559 = star_type' env e  in
              let uu____66562 =
                let uu____66579 =
                  let uu____66588 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____66588  in
                (uu____66579, FStar_Pervasives_Native.None)  in
              (uu____66559, uu____66562, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66532  in
          mk1 uu____66531
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____66629,(uu____66630,FStar_Pervasives_Native.Some uu____66631),uu____66632)
          ->
          let uu____66681 =
            let uu____66687 =
              let uu____66689 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____66689
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66687)  in
          FStar_Errors.raise_err uu____66681
      | FStar_Syntax_Syntax.Tm_refine uu____66693 ->
          let uu____66700 =
            let uu____66706 =
              let uu____66708 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____66708
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66706)  in
          FStar_Errors.raise_err uu____66700
      | FStar_Syntax_Syntax.Tm_uinst uu____66712 ->
          let uu____66719 =
            let uu____66725 =
              let uu____66727 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____66727
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66725)  in
          FStar_Errors.raise_err uu____66719
      | FStar_Syntax_Syntax.Tm_quoted uu____66731 ->
          let uu____66738 =
            let uu____66744 =
              let uu____66746 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____66746
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66744)  in
          FStar_Errors.raise_err uu____66738
      | FStar_Syntax_Syntax.Tm_constant uu____66750 ->
          let uu____66751 =
            let uu____66757 =
              let uu____66759 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____66759
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66757)  in
          FStar_Errors.raise_err uu____66751
      | FStar_Syntax_Syntax.Tm_match uu____66763 ->
          let uu____66786 =
            let uu____66792 =
              let uu____66794 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____66794
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66792)  in
          FStar_Errors.raise_err uu____66786
      | FStar_Syntax_Syntax.Tm_let uu____66798 ->
          let uu____66812 =
            let uu____66818 =
              let uu____66820 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____66820
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66818)  in
          FStar_Errors.raise_err uu____66812
      | FStar_Syntax_Syntax.Tm_uvar uu____66824 ->
          let uu____66837 =
            let uu____66843 =
              let uu____66845 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____66845
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66843)  in
          FStar_Errors.raise_err uu____66837
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____66849 =
            let uu____66855 =
              let uu____66857 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____66857
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66855)  in
          FStar_Errors.raise_err uu____66849
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66862 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____66862
      | FStar_Syntax_Syntax.Tm_delayed uu____66865 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_66897  ->
    match uu___588_66897 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_66908  ->
                match uu___587_66908 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____66911 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____66921 =
      let uu____66922 = FStar_Syntax_Subst.compress t  in
      uu____66922.FStar_Syntax_Syntax.n  in
    match uu____66921 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____66954 =
            let uu____66955 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____66955  in
          is_C uu____66954  in
        if r
        then
          ((let uu____66979 =
              let uu____66981 =
                FStar_List.for_all
                  (fun uu____66992  ->
                     match uu____66992 with | (h,uu____67001) -> is_C h) args
                 in
              Prims.op_Negation uu____66981  in
            if uu____66979 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____67014 =
              let uu____67016 =
                FStar_List.for_all
                  (fun uu____67028  ->
                     match uu____67028 with
                     | (h,uu____67037) ->
                         let uu____67042 = is_C h  in
                         Prims.op_Negation uu____67042) args
                 in
              Prims.op_Negation uu____67016  in
            if uu____67014 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____67071 = nm_of_comp comp  in
        (match uu____67071 with
         | M t1 ->
             ((let uu____67075 = is_C t1  in
               if uu____67075 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____67084) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____67090) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____67096,uu____67097) -> is_C t1
    | uu____67138 -> false
  
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
          let uu____67174 =
            let uu____67175 =
              let uu____67192 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____67195 =
                let uu____67206 =
                  let uu____67215 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____67215)  in
                [uu____67206]  in
              (uu____67192, uu____67195)  in
            FStar_Syntax_Syntax.Tm_app uu____67175  in
          mk1 uu____67174  in
        let uu____67251 =
          let uu____67252 = FStar_Syntax_Syntax.mk_binder p  in [uu____67252]
           in
        FStar_Syntax_Util.abs uu____67251 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_67277  ->
    match uu___589_67277 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____67280 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____67518 =
          match uu____67518 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____67555 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____67558 =
                       let uu____67560 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____67560  in
                     Prims.op_Negation uu____67558)
                   in
                if uu____67555
                then
                  let uu____67562 =
                    let uu____67568 =
                      let uu____67570 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____67572 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____67574 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____67570 uu____67572 uu____67574
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____67568)  in
                  FStar_Errors.raise_err uu____67562
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____67599 = mk_return env t1 s_e  in
                     ((M t1), uu____67599, u_e)))
               | (M t1,N t2) ->
                   let uu____67606 =
                     let uu____67612 =
                       let uu____67614 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____67616 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____67618 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____67614 uu____67616 uu____67618
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____67612)
                      in
                   FStar_Errors.raise_err uu____67606)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_67670 =
            match uu___590_67670 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____67686 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____67707 =
                let uu____67713 =
                  let uu____67715 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____67715
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____67713)  in
              FStar_Errors.raise_error uu____67707 e2.FStar_Syntax_Syntax.pos
          | M uu____67725 ->
              let uu____67726 = check env1 e2 context_nm  in
              strip_m uu____67726
           in
        let uu____67733 =
          let uu____67734 = FStar_Syntax_Subst.compress e  in
          uu____67734.FStar_Syntax_Syntax.n  in
        match uu____67733 with
        | FStar_Syntax_Syntax.Tm_bvar uu____67743 ->
            let uu____67744 = infer env e  in return_if uu____67744
        | FStar_Syntax_Syntax.Tm_name uu____67751 ->
            let uu____67752 = infer env e  in return_if uu____67752
        | FStar_Syntax_Syntax.Tm_fvar uu____67759 ->
            let uu____67760 = infer env e  in return_if uu____67760
        | FStar_Syntax_Syntax.Tm_abs uu____67767 ->
            let uu____67786 = infer env e  in return_if uu____67786
        | FStar_Syntax_Syntax.Tm_constant uu____67793 ->
            let uu____67794 = infer env e  in return_if uu____67794
        | FStar_Syntax_Syntax.Tm_quoted uu____67801 ->
            let uu____67808 = infer env e  in return_if uu____67808
        | FStar_Syntax_Syntax.Tm_app uu____67815 ->
            let uu____67832 = infer env e  in return_if uu____67832
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____67840 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____67840 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____67905) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____67911) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____67917,uu____67918) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____67959 ->
            let uu____67973 =
              let uu____67975 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____67975  in
            failwith uu____67973
        | FStar_Syntax_Syntax.Tm_type uu____67984 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____67992 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____68014 ->
            let uu____68021 =
              let uu____68023 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____68023  in
            failwith uu____68021
        | FStar_Syntax_Syntax.Tm_uvar uu____68032 ->
            let uu____68045 =
              let uu____68047 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____68047  in
            failwith uu____68045
        | FStar_Syntax_Syntax.Tm_delayed uu____68056 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____68086 =
              let uu____68088 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____68088  in
            failwith uu____68086

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
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env.tcenv
         in
      let uu____68118 =
        let uu____68119 = FStar_Syntax_Subst.compress e  in
        uu____68119.FStar_Syntax_Syntax.n  in
      match uu____68118 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____68138 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____68138
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____68189;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____68190;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____68196 =
                  let uu___1360_68197 = rc  in
                  let uu____68198 =
                    let uu____68203 =
                      let uu____68206 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____68206  in
                    FStar_Pervasives_Native.Some uu____68203  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_68197.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____68198;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_68197.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____68196
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_68218 = env  in
            let uu____68219 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____68219;
              subst = (uu___1366_68218.subst);
              tc_const = (uu___1366_68218.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____68245  ->
                 match uu____68245 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_68268 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_68268.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_68268.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____68269 =
            FStar_List.fold_left
              (fun uu____68300  ->
                 fun uu____68301  ->
                   match (uu____68300, uu____68301) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____68359 = is_C c  in
                       if uu____68359
                       then
                         let xw =
                           let uu____68369 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____68369
                            in
                         let x =
                           let uu___1385_68372 = bv  in
                           let uu____68373 =
                             let uu____68376 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____68376  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_68372.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_68372.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____68373
                           }  in
                         let env3 =
                           let uu___1388_68378 = env2  in
                           let uu____68379 =
                             let uu____68382 =
                               let uu____68383 =
                                 let uu____68390 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____68390)  in
                               FStar_Syntax_Syntax.NT uu____68383  in
                             uu____68382 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_68378.tcenv);
                             subst = uu____68379;
                             tc_const = (uu___1388_68378.tc_const)
                           }  in
                         let uu____68395 =
                           let uu____68398 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____68399 =
                             let uu____68402 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____68402 :: acc  in
                           uu____68398 :: uu____68399  in
                         (env3, uu____68395)
                       else
                         (let x =
                            let uu___1391_68408 = bv  in
                            let uu____68409 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_68408.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_68408.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____68409
                            }  in
                          let uu____68412 =
                            let uu____68415 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____68415 :: acc  in
                          (env2, uu____68412))) (env1, []) binders1
             in
          (match uu____68269 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____68435 =
                 let check_what =
                   let uu____68461 = is_monadic rc_opt1  in
                   if uu____68461 then check_m else check_n  in
                 let uu____68478 = check_what env2 body1  in
                 match uu____68478 with
                 | (t,s_body,u_body) ->
                     let uu____68498 =
                       let uu____68501 =
                         let uu____68502 = is_monadic rc_opt1  in
                         if uu____68502 then M t else N t  in
                       comp_of_nm uu____68501  in
                     (uu____68498, s_body, u_body)
                  in
               (match uu____68435 with
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
                                 let uu____68542 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_68548  ->
                                           match uu___591_68548 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____68551 -> false))
                                    in
                                 if uu____68542
                                 then
                                   let uu____68554 =
                                     FStar_List.filter
                                       (fun uu___592_68558  ->
                                          match uu___592_68558 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____68561 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____68554
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____68572 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_68578  ->
                                         match uu___593_68578 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____68581 -> false))
                                  in
                               if uu____68572
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_68590  ->
                                        match uu___594_68590 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____68593 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____68595 =
                                   let uu____68596 =
                                     let uu____68601 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____68601
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____68596 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____68595
                               else
                                 (let uu____68608 =
                                    let uu___1432_68609 = rc  in
                                    let uu____68610 =
                                      let uu____68615 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____68615
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_68609.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____68610;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_68609.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____68608))
                       in
                    let uu____68620 =
                      let comp1 =
                        let uu____68628 = is_monadic rc_opt1  in
                        let uu____68630 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____68628 uu____68630
                         in
                      let uu____68631 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____68631,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____68620 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____68669 =
                             let uu____68670 =
                               let uu____68689 =
                                 let uu____68692 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____68692 s_rc_opt  in
                               (s_binders1, s_body1, uu____68689)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68670  in
                           mk1 uu____68669  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____68712 =
                             let uu____68713 =
                               let uu____68732 =
                                 let uu____68735 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____68735 u_rc_opt  in
                               (u_binders2, u_body2, uu____68732)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68713  in
                           mk1 uu____68712  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____68751;_};
            FStar_Syntax_Syntax.fv_delta = uu____68752;
            FStar_Syntax_Syntax.fv_qual = uu____68753;_}
          ->
          let uu____68756 =
            let uu____68761 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____68761  in
          (match uu____68756 with
           | (uu____68792,t) ->
               let uu____68794 =
                 let uu____68795 = normalize1 t  in N uu____68795  in
               (uu____68794, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____68796;
             FStar_Syntax_Syntax.vars = uu____68797;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____68876 = FStar_Syntax_Util.head_and_args e  in
          (match uu____68876 with
           | (unary_op1,uu____68900) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____68971;
             FStar_Syntax_Syntax.vars = uu____68972;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____69068 = FStar_Syntax_Util.head_and_args e  in
          (match uu____69068 with
           | (unary_op1,uu____69092) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69171;
             FStar_Syntax_Syntax.vars = uu____69172;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____69210 = infer env a  in
          (match uu____69210 with
           | (t,s,u) ->
               let uu____69226 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69226 with
                | (head1,uu____69250) ->
                    let uu____69275 =
                      let uu____69276 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____69276  in
                    let uu____69277 =
                      let uu____69278 =
                        let uu____69279 =
                          let uu____69296 =
                            let uu____69307 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69307]  in
                          (head1, uu____69296)  in
                        FStar_Syntax_Syntax.Tm_app uu____69279  in
                      mk1 uu____69278  in
                    let uu____69344 =
                      let uu____69345 =
                        let uu____69346 =
                          let uu____69363 =
                            let uu____69374 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69374]  in
                          (head1, uu____69363)  in
                        FStar_Syntax_Syntax.Tm_app uu____69346  in
                      mk1 uu____69345  in
                    (uu____69275, uu____69277, uu____69344)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69411;
             FStar_Syntax_Syntax.vars = uu____69412;_},(a1,uu____69414)::a2::[])
          ->
          let uu____69470 = infer env a1  in
          (match uu____69470 with
           | (t,s,u) ->
               let uu____69486 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69486 with
                | (head1,uu____69510) ->
                    let uu____69535 =
                      let uu____69536 =
                        let uu____69537 =
                          let uu____69554 =
                            let uu____69565 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69565; a2]  in
                          (head1, uu____69554)  in
                        FStar_Syntax_Syntax.Tm_app uu____69537  in
                      mk1 uu____69536  in
                    let uu____69610 =
                      let uu____69611 =
                        let uu____69612 =
                          let uu____69629 =
                            let uu____69640 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69640; a2]  in
                          (head1, uu____69629)  in
                        FStar_Syntax_Syntax.Tm_app uu____69612  in
                      mk1 uu____69611  in
                    (t, uu____69535, uu____69610)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69685;
             FStar_Syntax_Syntax.vars = uu____69686;_},uu____69687)
          ->
          let uu____69712 =
            let uu____69718 =
              let uu____69720 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69720
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69718)  in
          FStar_Errors.raise_error uu____69712 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69730;
             FStar_Syntax_Syntax.vars = uu____69731;_},uu____69732)
          ->
          let uu____69757 =
            let uu____69763 =
              let uu____69765 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69765
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69763)  in
          FStar_Errors.raise_error uu____69757 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____69801 = check_n env head1  in
          (match uu____69801 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____69824 =
                   let uu____69825 = FStar_Syntax_Subst.compress t  in
                   uu____69825.FStar_Syntax_Syntax.n  in
                 match uu____69824 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____69829 -> true
                 | uu____69845 -> false  in
               let rec flatten1 t =
                 let uu____69867 =
                   let uu____69868 = FStar_Syntax_Subst.compress t  in
                   uu____69868.FStar_Syntax_Syntax.n  in
                 match uu____69867 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____69887);
                                FStar_Syntax_Syntax.pos = uu____69888;
                                FStar_Syntax_Syntax.vars = uu____69889;_})
                     when is_arrow t1 ->
                     let uu____69918 = flatten1 t1  in
                     (match uu____69918 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____70018,uu____70019) -> flatten1 e1
                 | uu____70060 ->
                     let uu____70061 =
                       let uu____70067 =
                         let uu____70069 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____70069
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____70067)  in
                     FStar_Errors.raise_err uu____70061
                  in
               let uu____70087 = flatten1 t_head  in
               (match uu____70087 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____70162 =
                          let uu____70168 =
                            let uu____70170 = FStar_Util.string_of_int n1  in
                            let uu____70172 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____70174 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____70170 uu____70172 uu____70174
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____70168)
                           in
                        FStar_Errors.raise_err uu____70162)
                     else ();
                     (let uu____70180 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____70180 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____70233 args1 =
                            match uu____70233 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____70333 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____70333
                                 | (binders3,[]) ->
                                     let uu____70371 =
                                       let uu____70372 =
                                         let uu____70375 =
                                           let uu____70376 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____70376
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____70375
                                          in
                                       uu____70372.FStar_Syntax_Syntax.n  in
                                     (match uu____70371 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____70409 =
                                            let uu____70410 =
                                              let uu____70411 =
                                                let uu____70426 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____70426)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____70411
                                               in
                                            mk1 uu____70410  in
                                          N uu____70409
                                      | uu____70439 -> failwith "wat?")
                                 | ([],uu____70441::uu____70442) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____70495)::binders3,(arg,uu____70498)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____70585 = FStar_List.splitAt n' binders1
                             in
                          (match uu____70585 with
                           | (binders2,uu____70619) ->
                               let uu____70652 =
                                 let uu____70675 =
                                   FStar_List.map2
                                     (fun uu____70737  ->
                                        fun uu____70738  ->
                                          match (uu____70737, uu____70738)
                                          with
                                          | ((bv,uu____70786),(arg,q)) ->
                                              let uu____70815 =
                                                let uu____70816 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____70816.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____70815 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____70837 ->
                                                   let uu____70838 =
                                                     let uu____70845 =
                                                       star_type' env arg  in
                                                     (uu____70845, q)  in
                                                   (uu____70838, [(arg, q)])
                                               | uu____70882 ->
                                                   let uu____70883 =
                                                     check_n env arg  in
                                                   (match uu____70883 with
                                                    | (uu____70908,s_arg,u_arg)
                                                        ->
                                                        let uu____70911 =
                                                          let uu____70920 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____70920
                                                          then
                                                            let uu____70931 =
                                                              let uu____70938
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____70938,
                                                                q)
                                                               in
                                                            [uu____70931;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____70911))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____70675  in
                               (match uu____70652 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____71066 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____71079 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____71066, uu____71079)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____71148) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____71154) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____71160,uu____71161) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____71203 =
            let uu____71204 = env.tc_const c  in N uu____71204  in
          (uu____71203, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____71211 ->
          let uu____71225 =
            let uu____71227 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____71227  in
          failwith uu____71225
      | FStar_Syntax_Syntax.Tm_type uu____71236 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____71244 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____71266 ->
          let uu____71273 =
            let uu____71275 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____71275  in
          failwith uu____71273
      | FStar_Syntax_Syntax.Tm_uvar uu____71284 ->
          let uu____71297 =
            let uu____71299 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____71299  in
          failwith uu____71297
      | FStar_Syntax_Syntax.Tm_delayed uu____71308 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71338 =
            let uu____71340 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____71340  in
          failwith uu____71338

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
          let uu____71389 = check_n env e0  in
          match uu____71389 with
          | (uu____71402,s_e0,u_e0) ->
              let uu____71405 =
                let uu____71434 =
                  FStar_List.map
                    (fun b  ->
                       let uu____71495 = FStar_Syntax_Subst.open_branch b  in
                       match uu____71495 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_71537 = env  in
                             let uu____71538 =
                               let uu____71539 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____71539
                                in
                             {
                               tcenv = uu____71538;
                               subst = (uu___1707_71537.subst);
                               tc_const = (uu___1707_71537.tc_const)
                             }  in
                           let uu____71542 = f env1 body  in
                           (match uu____71542 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____71614 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____71434  in
              (match uu____71405 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____71720 = FStar_List.hd nms  in
                     match uu____71720 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_71729  ->
                          match uu___595_71729 with
                          | M uu____71731 -> true
                          | uu____71733 -> false) nms
                      in
                   let uu____71735 =
                     let uu____71772 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____71862  ->
                              match uu____71862 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____72046 =
                                         check env original_body (M t2)  in
                                       (match uu____72046 with
                                        | (uu____72083,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____72122,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____71772  in
                   (match uu____71735 with
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
                              (fun uu____72311  ->
                                 match uu____72311 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____72362 =
                                         let uu____72363 =
                                           let uu____72380 =
                                             let uu____72391 =
                                               let uu____72400 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____72403 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____72400, uu____72403)  in
                                             [uu____72391]  in
                                           (s_body, uu____72380)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____72363
                                          in
                                       mk1 uu____72362  in
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
                            let uu____72538 =
                              let uu____72539 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____72539]  in
                            let uu____72558 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____72538 uu____72558
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____72582 =
                              let uu____72591 =
                                let uu____72598 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____72598
                                 in
                              [uu____72591]  in
                            let uu____72617 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____72582 uu____72617
                             in
                          let uu____72620 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____72659 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____72620, uu____72659)
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
                           let uu____72769 =
                             let uu____72770 =
                               let uu____72771 =
                                 let uu____72798 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____72798,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____72771
                                in
                             mk1 uu____72770  in
                           let uu____72857 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____72769, uu____72857))))

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
              let uu____72922 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____72922]  in
            let uu____72941 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____72941 with
            | (x_binders1,e21) ->
                let uu____72954 = infer env e1  in
                (match uu____72954 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____72971 = is_C t1  in
                       if uu____72971
                       then
                         let uu___1793_72974 = binding  in
                         let uu____72975 =
                           let uu____72978 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____72978  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_72974.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_72974.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____72975;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_72974.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_72974.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_72974.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_72974.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_72982 = env  in
                       let uu____72983 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_72985 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_72985.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_72985.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____72983;
                         subst = (uu___1796_72982.subst);
                         tc_const = (uu___1796_72982.tc_const)
                       }  in
                     let uu____72986 = proceed env1 e21  in
                     (match uu____72986 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_73003 = binding  in
                            let uu____73004 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_73003.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_73003.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____73004;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_73003.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_73003.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_73003.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_73003.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____73007 =
                            let uu____73008 =
                              let uu____73009 =
                                let uu____73023 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_73040 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_73040.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_73040.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_73040.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_73040.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_73040.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_73040.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73023)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73009  in
                            mk1 uu____73008  in
                          let uu____73041 =
                            let uu____73042 =
                              let uu____73043 =
                                let uu____73057 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_73074 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_73074.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_73074.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_73074.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_73074.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_73074.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_73074.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73057)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73043  in
                            mk1 uu____73042  in
                          (nm_rec, uu____73007, uu____73041))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_73079 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_73079.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_73079.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_73079.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_73079.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_73079.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_73081 = env  in
                       let uu____73082 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_73084 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_73084.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_73084.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73082;
                         subst = (uu___1820_73081.subst);
                         tc_const = (uu___1820_73081.tc_const)
                       }  in
                     let uu____73085 = ensure_m env1 e21  in
                     (match uu____73085 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____73109 =
                              let uu____73110 =
                                let uu____73127 =
                                  let uu____73138 =
                                    let uu____73147 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____73150 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____73147, uu____73150)  in
                                  [uu____73138]  in
                                (s_e2, uu____73127)  in
                              FStar_Syntax_Syntax.Tm_app uu____73110  in
                            mk1 uu____73109  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____73192 =
                              let uu____73193 =
                                let uu____73210 =
                                  let uu____73221 =
                                    let uu____73230 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____73230)  in
                                  [uu____73221]  in
                                (s_e1, uu____73210)  in
                              FStar_Syntax_Syntax.Tm_app uu____73193  in
                            mk1 uu____73192  in
                          let uu____73266 =
                            let uu____73267 =
                              let uu____73268 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____73268]  in
                            FStar_Syntax_Util.abs uu____73267 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____73287 =
                            let uu____73288 =
                              let uu____73289 =
                                let uu____73303 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_73320 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_73320.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_73320.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_73320.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_73320.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_73320.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_73320.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73303)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73289  in
                            mk1 uu____73288  in
                          ((M t2), uu____73266, uu____73287)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73330 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____73330  in
      let uu____73331 = check env e mn  in
      match uu____73331 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73347 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73370 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____73370  in
      let uu____73371 = check env e mn  in
      match uu____73371 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73387 -> failwith "[check_m]: impossible"

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
        (let uu____73420 =
           let uu____73422 = is_C c  in Prims.op_Negation uu____73422  in
         if uu____73420 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____73436 =
           let uu____73437 = FStar_Syntax_Subst.compress c  in
           uu____73437.FStar_Syntax_Syntax.n  in
         match uu____73436 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____73466 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____73466 with
              | (wp_head,wp_args) ->
                  ((let uu____73510 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____73529 =
                           let uu____73531 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____73531
                            in
                         Prims.op_Negation uu____73529)
                       in
                    if uu____73510 then failwith "mismatch" else ());
                   (let uu____73544 =
                      let uu____73545 =
                        let uu____73562 =
                          FStar_List.map2
                            (fun uu____73600  ->
                               fun uu____73601  ->
                                 match (uu____73600, uu____73601) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____73663 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____73663
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____73672 =
                                         let uu____73674 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____73674 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____73672
                                       then
                                         let uu____73676 =
                                           let uu____73682 =
                                             let uu____73684 =
                                               print_implicit q  in
                                             let uu____73686 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____73684 uu____73686
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____73682)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____73676
                                       else ());
                                      (let uu____73692 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____73692, q)))) args wp_args
                           in
                        (head1, uu____73562)  in
                      FStar_Syntax_Syntax.Tm_app uu____73545  in
                    mk1 uu____73544)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____73738 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____73738 with
              | (binders_orig,comp1) ->
                  let uu____73745 =
                    let uu____73762 =
                      FStar_List.map
                        (fun uu____73802  ->
                           match uu____73802 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____73830 = is_C h  in
                               if uu____73830
                               then
                                 let w' =
                                   let uu____73846 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____73846
                                    in
                                 let uu____73848 =
                                   let uu____73857 =
                                     let uu____73866 =
                                       let uu____73873 =
                                         let uu____73874 =
                                           let uu____73875 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____73875  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____73874
                                          in
                                       (uu____73873, q)  in
                                     [uu____73866]  in
                                   (w', q) :: uu____73857  in
                                 (w', uu____73848)
                               else
                                 (let x =
                                    let uu____73909 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____73909
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____73762  in
                  (match uu____73745 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____73983 =
                           let uu____73986 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____73986
                            in
                         FStar_Syntax_Subst.subst_comp uu____73983 comp1  in
                       let app =
                         let uu____73990 =
                           let uu____73991 =
                             let uu____74008 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____74027 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____74028 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____74027, uu____74028)) bvs
                                in
                             (wp, uu____74008)  in
                           FStar_Syntax_Syntax.Tm_app uu____73991  in
                         mk1 uu____73990  in
                       let comp3 =
                         let uu____74043 = type_of_comp comp2  in
                         let uu____74044 = is_monadic_comp comp2  in
                         trans_G env uu____74043 uu____74044 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____74047,uu____74048) ->
             trans_F_ env e wp
         | uu____74089 -> failwith "impossible trans_F_")

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
            let uu____74097 =
              let uu____74098 = star_type' env h  in
              let uu____74101 =
                let uu____74112 =
                  let uu____74121 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____74121)  in
                [uu____74112]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____74098;
                FStar_Syntax_Syntax.effect_args = uu____74101;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____74097
          else
            (let uu____74147 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____74147)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____74168 = n env.tcenv t  in star_type' env uu____74168
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____74188 = n env.tcenv t  in check_n env uu____74188
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____74205 = n env.tcenv c  in
        let uu____74206 = n env.tcenv wp  in
        trans_F_ env uu____74205 uu____74206
  