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
              let uu___613_61041 = a  in
              let uu____61042 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_61041.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_61041.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____61042
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____61055 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____61055
             then
               (d "Elaborating extra WP combinators";
                (let uu____61061 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____61061))
             else ());
            (let rec collect_binders t =
               let uu____61080 =
                 let uu____61081 =
                   let uu____61084 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____61084
                    in
                 uu____61081.FStar_Syntax_Syntax.n  in
               match uu____61080 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____61119) -> t1
                     | uu____61128 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____61130 = collect_binders rest  in
                   FStar_List.append bs uu____61130
               | FStar_Syntax_Syntax.Tm_type uu____61145 -> []
               | uu____61152 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____61179 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____61179
                 FStar_Syntax_Util.name_binders
                in
             (let uu____61205 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____61205
              then
                let uu____61209 =
                  let uu____61211 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____61211  in
                d uu____61209
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____61249 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____61249 with
                | (sigelt,fv) ->
                    ((let uu____61257 =
                        let uu____61260 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____61260
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____61257);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____61340  ->
                     match uu____61340 with
                     | (t,b) ->
                         let uu____61354 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____61354))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____61393 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____61393))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____61427 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____61427)
                 in
              let uu____61430 =
                let uu____61447 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____61472 =
                        let uu____61475 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____61475  in
                      FStar_Syntax_Util.arrow gamma uu____61472  in
                    let uu____61476 =
                      let uu____61477 =
                        let uu____61486 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____61493 =
                          let uu____61502 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____61502]  in
                        uu____61486 :: uu____61493  in
                      FStar_List.append binders uu____61477  in
                    FStar_Syntax_Util.abs uu____61476 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____61533 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____61534 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____61533, uu____61534)  in
                match uu____61447 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____61576 =
                        let uu____61577 =
                          let uu____61594 =
                            let uu____61605 =
                              FStar_List.map
                                (fun uu____61627  ->
                                   match uu____61627 with
                                   | (bv,uu____61639) ->
                                       let uu____61644 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____61645 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____61644, uu____61645)) binders
                               in
                            let uu____61647 =
                              let uu____61654 =
                                let uu____61659 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____61660 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____61659, uu____61660)  in
                              let uu____61662 =
                                let uu____61669 =
                                  let uu____61674 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____61674)  in
                                [uu____61669]  in
                              uu____61654 :: uu____61662  in
                            FStar_List.append uu____61605 uu____61647  in
                          (fv, uu____61594)  in
                        FStar_Syntax_Syntax.Tm_app uu____61577  in
                      mk1 uu____61576  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____61430 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____61747 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____61747
                       in
                    let ret1 =
                      let uu____61752 =
                        let uu____61753 =
                          let uu____61756 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____61756  in
                        FStar_Syntax_Util.residual_tot uu____61753  in
                      FStar_Pervasives_Native.Some uu____61752  in
                    let body =
                      let uu____61760 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____61760 ret1  in
                    let uu____61763 =
                      let uu____61764 = mk_all_implicit binders  in
                      let uu____61771 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____61764 uu____61771  in
                    FStar_Syntax_Util.abs uu____61763 body ret1  in
                  let c_pure1 =
                    let uu____61809 = mk_lid "pure"  in
                    register env1 uu____61809 c_pure  in
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
                      let uu____61819 =
                        let uu____61820 =
                          let uu____61821 =
                            let uu____61830 =
                              let uu____61837 =
                                let uu____61838 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____61838
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____61837  in
                            [uu____61830]  in
                          let uu____61851 =
                            let uu____61854 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____61854  in
                          FStar_Syntax_Util.arrow uu____61821 uu____61851  in
                        mk_gctx uu____61820  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____61819
                       in
                    let r =
                      let uu____61857 =
                        let uu____61858 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____61858  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____61857
                       in
                    let ret1 =
                      let uu____61863 =
                        let uu____61864 =
                          let uu____61867 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____61867  in
                        FStar_Syntax_Util.residual_tot uu____61864  in
                      FStar_Pervasives_Native.Some uu____61863  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____61877 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____61880 =
                          let uu____61891 =
                            let uu____61894 =
                              let uu____61895 =
                                let uu____61896 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____61896
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____61895  in
                            [uu____61894]  in
                          FStar_List.append gamma_as_args uu____61891  in
                        FStar_Syntax_Util.mk_app uu____61877 uu____61880  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____61899 =
                      let uu____61900 = mk_all_implicit binders  in
                      let uu____61907 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____61900 uu____61907  in
                    FStar_Syntax_Util.abs uu____61899 outer_body ret1  in
                  let c_app1 =
                    let uu____61959 = mk_lid "app"  in
                    register env1 uu____61959 c_app  in
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
                      let uu____61971 =
                        let uu____61980 =
                          let uu____61987 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____61987  in
                        [uu____61980]  in
                      let uu____62000 =
                        let uu____62003 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62003  in
                      FStar_Syntax_Util.arrow uu____61971 uu____62000  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62007 =
                        let uu____62008 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62008  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62007
                       in
                    let ret1 =
                      let uu____62013 =
                        let uu____62014 =
                          let uu____62017 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62017  in
                        FStar_Syntax_Util.residual_tot uu____62014  in
                      FStar_Pervasives_Native.Some uu____62013  in
                    let uu____62018 =
                      let uu____62019 = mk_all_implicit binders  in
                      let uu____62026 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____62019 uu____62026  in
                    let uu____62077 =
                      let uu____62080 =
                        let uu____62091 =
                          let uu____62094 =
                            let uu____62095 =
                              let uu____62106 =
                                let uu____62109 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____62109]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62106
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62095  in
                          let uu____62118 =
                            let uu____62121 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____62121]  in
                          uu____62094 :: uu____62118  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62091
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62080  in
                    FStar_Syntax_Util.abs uu____62018 uu____62077 ret1  in
                  let c_lift11 =
                    let uu____62131 = mk_lid "lift1"  in
                    register env1 uu____62131 c_lift1  in
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
                      let uu____62145 =
                        let uu____62154 =
                          let uu____62161 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62161  in
                        let uu____62162 =
                          let uu____62171 =
                            let uu____62178 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____62178  in
                          [uu____62171]  in
                        uu____62154 :: uu____62162  in
                      let uu____62197 =
                        let uu____62200 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62200  in
                      FStar_Syntax_Util.arrow uu____62145 uu____62197  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62204 =
                        let uu____62205 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62205  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62204
                       in
                    let a2 =
                      let uu____62208 =
                        let uu____62209 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____62209  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____62208
                       in
                    let ret1 =
                      let uu____62214 =
                        let uu____62215 =
                          let uu____62218 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____62218  in
                        FStar_Syntax_Util.residual_tot uu____62215  in
                      FStar_Pervasives_Native.Some uu____62214  in
                    let uu____62219 =
                      let uu____62220 = mk_all_implicit binders  in
                      let uu____62227 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____62220 uu____62227  in
                    let uu____62292 =
                      let uu____62295 =
                        let uu____62306 =
                          let uu____62309 =
                            let uu____62310 =
                              let uu____62321 =
                                let uu____62324 =
                                  let uu____62325 =
                                    let uu____62336 =
                                      let uu____62339 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____62339]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____62336
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____62325
                                   in
                                let uu____62348 =
                                  let uu____62351 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____62351]  in
                                uu____62324 :: uu____62348  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62321
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____62310  in
                          let uu____62360 =
                            let uu____62363 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____62363]  in
                          uu____62309 :: uu____62360  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62306
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62295  in
                    FStar_Syntax_Util.abs uu____62219 uu____62292 ret1  in
                  let c_lift21 =
                    let uu____62373 = mk_lid "lift2"  in
                    register env1 uu____62373 c_lift2  in
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
                      let uu____62385 =
                        let uu____62394 =
                          let uu____62401 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62401  in
                        [uu____62394]  in
                      let uu____62414 =
                        let uu____62417 =
                          let uu____62418 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62418  in
                        FStar_Syntax_Syntax.mk_Total uu____62417  in
                      FStar_Syntax_Util.arrow uu____62385 uu____62414  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____62424 =
                        let uu____62425 =
                          let uu____62428 =
                            let uu____62429 =
                              let uu____62438 =
                                let uu____62445 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____62445
                                 in
                              [uu____62438]  in
                            let uu____62458 =
                              let uu____62461 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____62461  in
                            FStar_Syntax_Util.arrow uu____62429 uu____62458
                             in
                          mk_ctx uu____62428  in
                        FStar_Syntax_Util.residual_tot uu____62425  in
                      FStar_Pervasives_Native.Some uu____62424  in
                    let e1 =
                      let uu____62463 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____62463
                       in
                    let body =
                      let uu____62468 =
                        let uu____62469 =
                          let uu____62478 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____62478]  in
                        FStar_List.append gamma uu____62469  in
                      let uu____62503 =
                        let uu____62506 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____62509 =
                          let uu____62520 =
                            let uu____62521 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____62521  in
                          let uu____62522 = args_of_binders1 gamma  in
                          uu____62520 :: uu____62522  in
                        FStar_Syntax_Util.mk_app uu____62506 uu____62509  in
                      FStar_Syntax_Util.abs uu____62468 uu____62503 ret1  in
                    let uu____62525 =
                      let uu____62526 = mk_all_implicit binders  in
                      let uu____62533 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____62526 uu____62533  in
                    FStar_Syntax_Util.abs uu____62525 body ret1  in
                  let c_push1 =
                    let uu____62578 = mk_lid "push"  in
                    register env1 uu____62578 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____62605 =
                        let uu____62606 =
                          let uu____62623 = args_of_binders1 binders  in
                          (c, uu____62623)  in
                        FStar_Syntax_Syntax.Tm_app uu____62606  in
                      mk1 uu____62605
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____62652 =
                        let uu____62653 =
                          let uu____62662 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____62669 =
                            let uu____62678 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____62678]  in
                          uu____62662 :: uu____62669  in
                        let uu____62703 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____62653 uu____62703  in
                      FStar_Syntax_Syntax.mk_Total uu____62652  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____62708 =
                      let uu____62709 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____62709  in
                    let uu____62724 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____62729 =
                        let uu____62732 =
                          let uu____62743 =
                            let uu____62746 =
                              let uu____62747 =
                                let uu____62758 =
                                  let uu____62767 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____62767  in
                                [uu____62758]  in
                              FStar_Syntax_Util.mk_app l_ite uu____62747  in
                            [uu____62746]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____62743
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____62732  in
                      FStar_Syntax_Util.ascribe uu____62729
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____62708 uu____62724
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____62811 = mk_lid "wp_if_then_else"  in
                    register env1 uu____62811 wp_if_then_else  in
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
                      let uu____62828 =
                        let uu____62839 =
                          let uu____62842 =
                            let uu____62843 =
                              let uu____62854 =
                                let uu____62857 =
                                  let uu____62858 =
                                    let uu____62869 =
                                      let uu____62878 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62878
                                       in
                                    [uu____62869]  in
                                  FStar_Syntax_Util.mk_app l_and uu____62858
                                   in
                                [uu____62857]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62854
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62843  in
                          let uu____62903 =
                            let uu____62906 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____62906]  in
                          uu____62842 :: uu____62903  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62839
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62828  in
                    let uu____62915 =
                      let uu____62916 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____62916  in
                    FStar_Syntax_Util.abs uu____62915 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____62932 = mk_lid "wp_assert"  in
                    register env1 uu____62932 wp_assert  in
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
                      let uu____62949 =
                        let uu____62960 =
                          let uu____62963 =
                            let uu____62964 =
                              let uu____62975 =
                                let uu____62978 =
                                  let uu____62979 =
                                    let uu____62990 =
                                      let uu____62999 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62999
                                       in
                                    [uu____62990]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____62979
                                   in
                                [uu____62978]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62975
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62964  in
                          let uu____63024 =
                            let uu____63027 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____63027]  in
                          uu____62963 :: uu____63024  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62960
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62949  in
                    let uu____63036 =
                      let uu____63037 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____63037  in
                    FStar_Syntax_Util.abs uu____63036 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____63053 = mk_lid "wp_assume"  in
                    register env1 uu____63053 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____63066 =
                        let uu____63075 =
                          let uu____63082 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____63082  in
                        [uu____63075]  in
                      let uu____63095 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____63066 uu____63095  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____63103 =
                        let uu____63114 =
                          let uu____63117 =
                            let uu____63118 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____63118  in
                          let uu____63137 =
                            let uu____63140 =
                              let uu____63141 =
                                let uu____63152 =
                                  let uu____63155 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____63155]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____63152
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____63141
                               in
                            [uu____63140]  in
                          uu____63117 :: uu____63137  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63114
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63103  in
                    let uu____63172 =
                      let uu____63173 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____63173  in
                    FStar_Syntax_Util.abs uu____63172 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____63189 = mk_lid "wp_close"  in
                    register env1 uu____63189 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____63200 =
                      let uu____63201 =
                        let uu____63202 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____63202
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____63201
                       in
                    FStar_Pervasives_Native.Some uu____63200  in
                  let mk_forall1 x body =
                    let uu____63214 =
                      let uu____63221 =
                        let uu____63222 =
                          let uu____63239 =
                            let uu____63250 =
                              let uu____63259 =
                                let uu____63260 =
                                  let uu____63261 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____63261]  in
                                FStar_Syntax_Util.abs uu____63260 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____63259  in
                            [uu____63250]  in
                          (FStar_Syntax_Util.tforall, uu____63239)  in
                        FStar_Syntax_Syntax.Tm_app uu____63222  in
                      FStar_Syntax_Syntax.mk uu____63221  in
                    uu____63214 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____63319 =
                      let uu____63320 = FStar_Syntax_Subst.compress t  in
                      uu____63320.FStar_Syntax_Syntax.n  in
                    match uu____63319 with
                    | FStar_Syntax_Syntax.Tm_type uu____63324 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63357  ->
                              match uu____63357 with
                              | (b,uu____63366) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____63371 -> true  in
                  let rec is_monotonic t =
                    let uu____63384 =
                      let uu____63385 = FStar_Syntax_Subst.compress t  in
                      uu____63385.FStar_Syntax_Syntax.n  in
                    match uu____63384 with
                    | FStar_Syntax_Syntax.Tm_type uu____63389 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63422  ->
                              match uu____63422 with
                              | (b,uu____63431) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____63436 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____63510 =
                      let uu____63511 = FStar_Syntax_Subst.compress t1  in
                      uu____63511.FStar_Syntax_Syntax.n  in
                    match uu____63510 with
                    | FStar_Syntax_Syntax.Tm_type uu____63516 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____63519);
                                      FStar_Syntax_Syntax.pos = uu____63520;
                                      FStar_Syntax_Syntax.vars = uu____63521;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63565 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63565
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63575 =
                              let uu____63578 =
                                let uu____63589 =
                                  let uu____63598 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63598  in
                                [uu____63589]  in
                              FStar_Syntax_Util.mk_app x uu____63578  in
                            let uu____63615 =
                              let uu____63618 =
                                let uu____63629 =
                                  let uu____63638 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63638  in
                                [uu____63629]  in
                              FStar_Syntax_Util.mk_app y uu____63618  in
                            mk_rel1 b uu____63575 uu____63615  in
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
                             let uu____63662 =
                               let uu____63665 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63668 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63665 uu____63668  in
                             let uu____63671 =
                               let uu____63674 =
                                 let uu____63677 =
                                   let uu____63688 =
                                     let uu____63697 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63697
                                      in
                                   [uu____63688]  in
                                 FStar_Syntax_Util.mk_app x uu____63677  in
                               let uu____63714 =
                                 let uu____63717 =
                                   let uu____63728 =
                                     let uu____63737 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63737
                                      in
                                   [uu____63728]  in
                                 FStar_Syntax_Util.mk_app y uu____63717  in
                               mk_rel1 b uu____63674 uu____63714  in
                             FStar_Syntax_Util.mk_imp uu____63662 uu____63671
                              in
                           let uu____63754 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63754)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____63757);
                                      FStar_Syntax_Syntax.pos = uu____63758;
                                      FStar_Syntax_Syntax.vars = uu____63759;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63803 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63803
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63813 =
                              let uu____63816 =
                                let uu____63827 =
                                  let uu____63836 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63836  in
                                [uu____63827]  in
                              FStar_Syntax_Util.mk_app x uu____63816  in
                            let uu____63853 =
                              let uu____63856 =
                                let uu____63867 =
                                  let uu____63876 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63876  in
                                [uu____63867]  in
                              FStar_Syntax_Util.mk_app y uu____63856  in
                            mk_rel1 b uu____63813 uu____63853  in
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
                             let uu____63900 =
                               let uu____63903 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63906 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63903 uu____63906  in
                             let uu____63909 =
                               let uu____63912 =
                                 let uu____63915 =
                                   let uu____63926 =
                                     let uu____63935 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63935
                                      in
                                   [uu____63926]  in
                                 FStar_Syntax_Util.mk_app x uu____63915  in
                               let uu____63952 =
                                 let uu____63955 =
                                   let uu____63966 =
                                     let uu____63975 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63975
                                      in
                                   [uu____63966]  in
                                 FStar_Syntax_Util.mk_app y uu____63955  in
                               mk_rel1 b uu____63912 uu____63952  in
                             FStar_Syntax_Util.mk_imp uu____63900 uu____63909
                              in
                           let uu____63992 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63992)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_64031 = t1  in
                          let uu____64032 =
                            let uu____64033 =
                              let uu____64048 =
                                let uu____64051 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____64051  in
                              ([binder], uu____64048)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____64033  in
                          {
                            FStar_Syntax_Syntax.n = uu____64032;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_64031.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_64031.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____64074 ->
                        failwith "unhandled arrow"
                    | uu____64092 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____64129 =
                        let uu____64130 = FStar_Syntax_Subst.compress t1  in
                        uu____64130.FStar_Syntax_Syntax.n  in
                      match uu____64129 with
                      | FStar_Syntax_Syntax.Tm_type uu____64133 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____64160 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____64160
                          ->
                          let project i tuple =
                            let projector =
                              let uu____64181 =
                                let uu____64182 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____64182 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____64181
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____64212 =
                            let uu____64223 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____64241  ->
                                     match uu____64241 with
                                     | (t2,q) ->
                                         let uu____64261 = project i x  in
                                         let uu____64264 = project i y  in
                                         mk_stronger t2 uu____64261
                                           uu____64264) args
                               in
                            match uu____64223 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____64212 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____64318);
                                      FStar_Syntax_Syntax.pos = uu____64319;
                                      FStar_Syntax_Syntax.vars = uu____64320;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64364  ->
                                   match uu____64364 with
                                   | (bv,q) ->
                                       let uu____64378 =
                                         let uu____64380 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64380  in
                                       FStar_Syntax_Syntax.gen_bv uu____64378
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64389 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64389) bvs
                             in
                          let body =
                            let uu____64391 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64394 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64391 uu____64394  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____64403);
                                      FStar_Syntax_Syntax.pos = uu____64404;
                                      FStar_Syntax_Syntax.vars = uu____64405;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64449  ->
                                   match uu____64449 with
                                   | (bv,q) ->
                                       let uu____64463 =
                                         let uu____64465 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64465  in
                                       FStar_Syntax_Syntax.gen_bv uu____64463
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64474 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64474) bvs
                             in
                          let body =
                            let uu____64476 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64479 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64476 uu____64479  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____64486 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____64489 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____64492 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____64495 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____64489 uu____64492 uu____64495  in
                    let uu____64498 =
                      let uu____64499 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____64499  in
                    FStar_Syntax_Util.abs uu____64498 body ret_tot_type  in
                  let stronger1 =
                    let uu____64541 = mk_lid "stronger"  in
                    register env1 uu____64541 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64549 = FStar_Util.prefix gamma  in
                    match uu____64549 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____64615 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____64615
                             in
                          let uu____64620 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____64620 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____64630 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____64630  in
                              let guard_free1 =
                                let uu____64642 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____64642  in
                              let pat =
                                let uu____64646 =
                                  let uu____64657 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____64657]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____64646
                                 in
                              let pattern_guarded_body =
                                let uu____64685 =
                                  let uu____64686 =
                                    let uu____64693 =
                                      let uu____64694 =
                                        let uu____64707 =
                                          let uu____64718 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____64718]  in
                                        [uu____64707]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____64694
                                       in
                                    (body, uu____64693)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____64686  in
                                mk1 uu____64685  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____64765 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____64774 =
                            let uu____64777 =
                              let uu____64778 =
                                let uu____64781 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____64784 =
                                  let uu____64795 = args_of_binders1 wp_args
                                     in
                                  let uu____64798 =
                                    let uu____64801 =
                                      let uu____64802 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____64802
                                       in
                                    [uu____64801]  in
                                  FStar_List.append uu____64795 uu____64798
                                   in
                                FStar_Syntax_Util.mk_app uu____64781
                                  uu____64784
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____64778  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____64777
                             in
                          FStar_Syntax_Util.abs gamma uu____64774
                            ret_gtot_type
                           in
                        let uu____64803 =
                          let uu____64804 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____64804  in
                        FStar_Syntax_Util.abs uu____64803 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____64820 = mk_lid "ite_wp"  in
                    register env1 uu____64820 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64828 = FStar_Util.prefix gamma  in
                    match uu____64828 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____64886 =
                            let uu____64887 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____64894 =
                              let uu____64905 =
                                let uu____64914 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____64914  in
                              [uu____64905]  in
                            FStar_Syntax_Util.mk_app uu____64887 uu____64894
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____64886
                           in
                        let uu____64931 =
                          let uu____64932 =
                            let uu____64941 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____64941 gamma  in
                          FStar_List.append binders uu____64932  in
                        FStar_Syntax_Util.abs uu____64931 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____64963 = mk_lid "null_wp"  in
                    register env1 uu____64963 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____64976 =
                        let uu____64987 =
                          let uu____64990 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____64991 =
                            let uu____64994 =
                              let uu____64995 =
                                let uu____65006 =
                                  let uu____65015 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____65015  in
                                [uu____65006]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____64995
                               in
                            let uu____65032 =
                              let uu____65035 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____65035]  in
                            uu____64994 :: uu____65032  in
                          uu____64990 :: uu____64991  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____64987
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____64976  in
                    let uu____65044 =
                      let uu____65045 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____65045  in
                    FStar_Syntax_Util.abs uu____65044 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____65061 = mk_lid "wp_trivial"  in
                    register env1 uu____65061 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____65067 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____65067
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____65079 =
                      let uu____65080 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____65080  in
                    let uu____65106 =
                      let uu___934_65107 = ed  in
                      let uu____65108 =
                        let uu____65109 = c wp_if_then_else2  in
                        ([], uu____65109)  in
                      let uu____65116 =
                        let uu____65117 = c ite_wp2  in ([], uu____65117)  in
                      let uu____65124 =
                        let uu____65125 = c stronger2  in ([], uu____65125)
                         in
                      let uu____65132 =
                        let uu____65133 = c wp_close2  in ([], uu____65133)
                         in
                      let uu____65140 =
                        let uu____65141 = c wp_assert2  in ([], uu____65141)
                         in
                      let uu____65148 =
                        let uu____65149 = c wp_assume2  in ([], uu____65149)
                         in
                      let uu____65156 =
                        let uu____65157 = c null_wp2  in ([], uu____65157)
                         in
                      let uu____65164 =
                        let uu____65165 = c wp_trivial2  in ([], uu____65165)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_65107.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_65107.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_65107.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_65107.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_65107.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_65107.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_65107.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____65108;
                        FStar_Syntax_Syntax.ite_wp = uu____65116;
                        FStar_Syntax_Syntax.stronger = uu____65124;
                        FStar_Syntax_Syntax.close_wp = uu____65132;
                        FStar_Syntax_Syntax.assert_p = uu____65140;
                        FStar_Syntax_Syntax.assume_p = uu____65148;
                        FStar_Syntax_Syntax.null_wp = uu____65156;
                        FStar_Syntax_Syntax.trivial = uu____65164;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_65107.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_65107.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_65107.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_65107.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_65107.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____65079, uu____65106)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_65189 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_65189.subst);
        tc_const = (uu___939_65189.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____65210 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____65229 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65249) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_65263  ->
                match uu___585_65263 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____65266 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____65268 ->
        let uu____65269 =
          let uu____65275 =
            let uu____65277 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____65277
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____65275)  in
        FStar_Errors.raise_error uu____65269 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_65287  ->
    match uu___586_65287 with
    | N t ->
        let uu____65290 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____65290
    | M t ->
        let uu____65294 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____65294
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____65303,c) -> nm_of_comp c
    | uu____65325 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____65338 = nm_of_comp c  in
    match uu____65338 with | M uu____65340 -> true | N uu____65342 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____65353 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____65369 =
        let uu____65378 =
          let uu____65385 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____65385  in
        [uu____65378]  in
      let uu____65404 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____65369 uu____65404  in
    let uu____65407 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____65407
  
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
        let uu____65449 =
          let uu____65450 =
            let uu____65465 =
              let uu____65474 =
                let uu____65481 =
                  let uu____65482 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____65482  in
                let uu____65483 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____65481, uu____65483)  in
              [uu____65474]  in
            let uu____65501 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____65465, uu____65501)  in
          FStar_Syntax_Syntax.Tm_arrow uu____65450  in
        mk1 uu____65449

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____65541) ->
          let binders1 =
            FStar_List.map
              (fun uu____65587  ->
                 match uu____65587 with
                 | (bv,aqual) ->
                     let uu____65606 =
                       let uu___989_65607 = bv  in
                       let uu____65608 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_65607.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_65607.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____65608
                       }  in
                     (uu____65606, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____65613,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____65615);
                              FStar_Syntax_Syntax.pos = uu____65616;
                              FStar_Syntax_Syntax.vars = uu____65617;_})
               ->
               let uu____65646 =
                 let uu____65647 =
                   let uu____65662 =
                     let uu____65665 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____65665  in
                   (binders1, uu____65662)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____65647  in
               mk1 uu____65646
           | uu____65676 ->
               let uu____65677 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____65677 with
                | N hn ->
                    let uu____65679 =
                      let uu____65680 =
                        let uu____65695 =
                          let uu____65698 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____65698  in
                        (binders1, uu____65695)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65680  in
                    mk1 uu____65679
                | M a ->
                    let uu____65710 =
                      let uu____65711 =
                        let uu____65726 =
                          let uu____65735 =
                            let uu____65744 =
                              let uu____65751 =
                                let uu____65752 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____65752  in
                              let uu____65753 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____65751, uu____65753)  in
                            [uu____65744]  in
                          FStar_List.append binders1 uu____65735  in
                        let uu____65777 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____65726, uu____65777)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65711  in
                    mk1 uu____65710))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____65871 = f x  in
                    FStar_Util.string_builder_append strb uu____65871);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____65880 = f x1  in
                         FStar_Util.string_builder_append strb uu____65880))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____65884 =
              let uu____65890 =
                let uu____65892 = FStar_Syntax_Print.term_to_string t2  in
                let uu____65894 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____65892 uu____65894
                 in
              (FStar_Errors.Warning_DependencyFound, uu____65890)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____65884  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____65916 =
              let uu____65917 = FStar_Syntax_Subst.compress ty  in
              uu____65917.FStar_Syntax_Syntax.n  in
            match uu____65916 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____65943 =
                  let uu____65945 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____65945  in
                if uu____65943
                then false
                else
                  (try
                     (fun uu___1038_65962  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____65986 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____65986 s  in
                              let uu____65989 =
                                let uu____65991 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____65991  in
                              if uu____65989
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____65997 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____65997 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____66022  ->
                                          match uu____66022 with
                                          | (bv,uu____66034) ->
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
            | uu____66062 ->
                ((let uu____66064 =
                    let uu____66070 =
                      let uu____66072 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____66072
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____66070)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____66064);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____66088 =
              let uu____66089 = FStar_Syntax_Subst.compress head2  in
              uu____66089.FStar_Syntax_Syntax.n  in
            match uu____66088 with
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
                  (let uu____66095 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____66095)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____66098 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____66098 with
                 | ((uu____66108,ty),uu____66110) ->
                     let uu____66115 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____66115
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____66128 =
                         let uu____66129 = FStar_Syntax_Subst.compress res
                            in
                         uu____66129.FStar_Syntax_Syntax.n  in
                       (match uu____66128 with
                        | FStar_Syntax_Syntax.Tm_app uu____66133 -> true
                        | uu____66151 ->
                            ((let uu____66153 =
                                let uu____66159 =
                                  let uu____66161 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____66161
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____66159)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____66153);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____66169 -> true
            | FStar_Syntax_Syntax.Tm_name uu____66171 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____66174) ->
                is_valid_application t2
            | uu____66179 -> false  in
          let uu____66181 = is_valid_application head1  in
          if uu____66181
          then
            let uu____66184 =
              let uu____66185 =
                let uu____66202 =
                  FStar_List.map
                    (fun uu____66231  ->
                       match uu____66231 with
                       | (t2,qual) ->
                           let uu____66256 = star_type' env t2  in
                           (uu____66256, qual)) args
                   in
                (head1, uu____66202)  in
              FStar_Syntax_Syntax.Tm_app uu____66185  in
            mk1 uu____66184
          else
            (let uu____66273 =
               let uu____66279 =
                 let uu____66281 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____66281
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____66279)  in
             FStar_Errors.raise_err uu____66273)
      | FStar_Syntax_Syntax.Tm_bvar uu____66285 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____66286 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____66287 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____66288 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____66316 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____66316 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_66324 = env  in
                 let uu____66325 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____66325;
                   subst = (uu___1110_66324.subst);
                   tc_const = (uu___1110_66324.tc_const)
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
               ((let uu___1125_66352 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_66352.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_66352.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____66359 =
            let uu____66360 =
              let uu____66367 = star_type' env t2  in (uu____66367, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____66360  in
          mk1 uu____66359
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____66419 =
            let uu____66420 =
              let uu____66447 = star_type' env e  in
              let uu____66450 =
                let uu____66467 =
                  let uu____66476 = star_type' env t2  in
                  FStar_Util.Inl uu____66476  in
                (uu____66467, FStar_Pervasives_Native.None)  in
              (uu____66447, uu____66450, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66420  in
          mk1 uu____66419
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____66564 =
            let uu____66565 =
              let uu____66592 = star_type' env e  in
              let uu____66595 =
                let uu____66612 =
                  let uu____66621 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____66621  in
                (uu____66612, FStar_Pervasives_Native.None)  in
              (uu____66592, uu____66595, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66565  in
          mk1 uu____66564
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____66662,(uu____66663,FStar_Pervasives_Native.Some uu____66664),uu____66665)
          ->
          let uu____66714 =
            let uu____66720 =
              let uu____66722 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____66722
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66720)  in
          FStar_Errors.raise_err uu____66714
      | FStar_Syntax_Syntax.Tm_refine uu____66726 ->
          let uu____66733 =
            let uu____66739 =
              let uu____66741 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____66741
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66739)  in
          FStar_Errors.raise_err uu____66733
      | FStar_Syntax_Syntax.Tm_uinst uu____66745 ->
          let uu____66752 =
            let uu____66758 =
              let uu____66760 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____66760
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66758)  in
          FStar_Errors.raise_err uu____66752
      | FStar_Syntax_Syntax.Tm_quoted uu____66764 ->
          let uu____66771 =
            let uu____66777 =
              let uu____66779 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____66779
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66777)  in
          FStar_Errors.raise_err uu____66771
      | FStar_Syntax_Syntax.Tm_constant uu____66783 ->
          let uu____66784 =
            let uu____66790 =
              let uu____66792 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____66792
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66790)  in
          FStar_Errors.raise_err uu____66784
      | FStar_Syntax_Syntax.Tm_match uu____66796 ->
          let uu____66819 =
            let uu____66825 =
              let uu____66827 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____66827
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66825)  in
          FStar_Errors.raise_err uu____66819
      | FStar_Syntax_Syntax.Tm_let uu____66831 ->
          let uu____66845 =
            let uu____66851 =
              let uu____66853 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____66853
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66851)  in
          FStar_Errors.raise_err uu____66845
      | FStar_Syntax_Syntax.Tm_uvar uu____66857 ->
          let uu____66870 =
            let uu____66876 =
              let uu____66878 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____66878
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66876)  in
          FStar_Errors.raise_err uu____66870
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____66882 =
            let uu____66888 =
              let uu____66890 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____66890
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66888)  in
          FStar_Errors.raise_err uu____66882
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66895 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____66895
      | FStar_Syntax_Syntax.Tm_delayed uu____66898 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_66930  ->
    match uu___588_66930 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_66941  ->
                match uu___587_66941 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____66944 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____66954 =
      let uu____66955 = FStar_Syntax_Subst.compress t  in
      uu____66955.FStar_Syntax_Syntax.n  in
    match uu____66954 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____66987 =
            let uu____66988 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____66988  in
          is_C uu____66987  in
        if r
        then
          ((let uu____67012 =
              let uu____67014 =
                FStar_List.for_all
                  (fun uu____67025  ->
                     match uu____67025 with | (h,uu____67034) -> is_C h) args
                 in
              Prims.op_Negation uu____67014  in
            if uu____67012 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____67047 =
              let uu____67049 =
                FStar_List.for_all
                  (fun uu____67061  ->
                     match uu____67061 with
                     | (h,uu____67070) ->
                         let uu____67075 = is_C h  in
                         Prims.op_Negation uu____67075) args
                 in
              Prims.op_Negation uu____67049  in
            if uu____67047 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____67104 = nm_of_comp comp  in
        (match uu____67104 with
         | M t1 ->
             ((let uu____67108 = is_C t1  in
               if uu____67108 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____67117) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____67123) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____67129,uu____67130) -> is_C t1
    | uu____67171 -> false
  
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
          let uu____67207 =
            let uu____67208 =
              let uu____67225 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____67228 =
                let uu____67239 =
                  let uu____67248 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____67248)  in
                [uu____67239]  in
              (uu____67225, uu____67228)  in
            FStar_Syntax_Syntax.Tm_app uu____67208  in
          mk1 uu____67207  in
        let uu____67284 =
          let uu____67285 = FStar_Syntax_Syntax.mk_binder p  in [uu____67285]
           in
        FStar_Syntax_Util.abs uu____67284 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_67310  ->
    match uu___589_67310 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____67313 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____67551 =
          match uu____67551 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____67588 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____67591 =
                       let uu____67593 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____67593  in
                     Prims.op_Negation uu____67591)
                   in
                if uu____67588
                then
                  let uu____67595 =
                    let uu____67601 =
                      let uu____67603 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____67605 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____67607 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____67603 uu____67605 uu____67607
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____67601)  in
                  FStar_Errors.raise_err uu____67595
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____67632 = mk_return env t1 s_e  in
                     ((M t1), uu____67632, u_e)))
               | (M t1,N t2) ->
                   let uu____67639 =
                     let uu____67645 =
                       let uu____67647 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____67649 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____67651 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____67647 uu____67649 uu____67651
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____67645)
                      in
                   FStar_Errors.raise_err uu____67639)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_67703 =
            match uu___590_67703 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____67719 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____67740 =
                let uu____67746 =
                  let uu____67748 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____67748
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____67746)  in
              FStar_Errors.raise_error uu____67740 e2.FStar_Syntax_Syntax.pos
          | M uu____67758 ->
              let uu____67759 = check env1 e2 context_nm  in
              strip_m uu____67759
           in
        let uu____67766 =
          let uu____67767 = FStar_Syntax_Subst.compress e  in
          uu____67767.FStar_Syntax_Syntax.n  in
        match uu____67766 with
        | FStar_Syntax_Syntax.Tm_bvar uu____67776 ->
            let uu____67777 = infer env e  in return_if uu____67777
        | FStar_Syntax_Syntax.Tm_name uu____67784 ->
            let uu____67785 = infer env e  in return_if uu____67785
        | FStar_Syntax_Syntax.Tm_fvar uu____67792 ->
            let uu____67793 = infer env e  in return_if uu____67793
        | FStar_Syntax_Syntax.Tm_abs uu____67800 ->
            let uu____67819 = infer env e  in return_if uu____67819
        | FStar_Syntax_Syntax.Tm_constant uu____67826 ->
            let uu____67827 = infer env e  in return_if uu____67827
        | FStar_Syntax_Syntax.Tm_quoted uu____67834 ->
            let uu____67841 = infer env e  in return_if uu____67841
        | FStar_Syntax_Syntax.Tm_app uu____67848 ->
            let uu____67865 = infer env e  in return_if uu____67865
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____67873 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____67873 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____67938) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____67944) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____67950,uu____67951) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____67992 ->
            let uu____68006 =
              let uu____68008 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____68008  in
            failwith uu____68006
        | FStar_Syntax_Syntax.Tm_type uu____68017 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____68025 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____68047 ->
            let uu____68054 =
              let uu____68056 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____68056  in
            failwith uu____68054
        | FStar_Syntax_Syntax.Tm_uvar uu____68065 ->
            let uu____68078 =
              let uu____68080 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____68080  in
            failwith uu____68078
        | FStar_Syntax_Syntax.Tm_delayed uu____68089 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____68119 =
              let uu____68121 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____68121  in
            failwith uu____68119

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
      let uu____68151 =
        let uu____68152 = FStar_Syntax_Subst.compress e  in
        uu____68152.FStar_Syntax_Syntax.n  in
      match uu____68151 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____68171 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____68171
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____68222;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____68223;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____68229 =
                  let uu___1360_68230 = rc  in
                  let uu____68231 =
                    let uu____68236 =
                      let uu____68239 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____68239  in
                    FStar_Pervasives_Native.Some uu____68236  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_68230.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____68231;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_68230.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____68229
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_68251 = env  in
            let uu____68252 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____68252;
              subst = (uu___1366_68251.subst);
              tc_const = (uu___1366_68251.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____68278  ->
                 match uu____68278 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_68301 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_68301.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_68301.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____68302 =
            FStar_List.fold_left
              (fun uu____68333  ->
                 fun uu____68334  ->
                   match (uu____68333, uu____68334) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____68392 = is_C c  in
                       if uu____68392
                       then
                         let xw =
                           let uu____68402 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____68402
                            in
                         let x =
                           let uu___1385_68405 = bv  in
                           let uu____68406 =
                             let uu____68409 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____68409  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_68405.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_68405.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____68406
                           }  in
                         let env3 =
                           let uu___1388_68411 = env2  in
                           let uu____68412 =
                             let uu____68415 =
                               let uu____68416 =
                                 let uu____68423 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____68423)  in
                               FStar_Syntax_Syntax.NT uu____68416  in
                             uu____68415 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_68411.tcenv);
                             subst = uu____68412;
                             tc_const = (uu___1388_68411.tc_const)
                           }  in
                         let uu____68428 =
                           let uu____68431 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____68432 =
                             let uu____68435 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____68435 :: acc  in
                           uu____68431 :: uu____68432  in
                         (env3, uu____68428)
                       else
                         (let x =
                            let uu___1391_68441 = bv  in
                            let uu____68442 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_68441.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_68441.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____68442
                            }  in
                          let uu____68445 =
                            let uu____68448 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____68448 :: acc  in
                          (env2, uu____68445))) (env1, []) binders1
             in
          (match uu____68302 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____68468 =
                 let check_what =
                   let uu____68494 = is_monadic rc_opt1  in
                   if uu____68494 then check_m else check_n  in
                 let uu____68511 = check_what env2 body1  in
                 match uu____68511 with
                 | (t,s_body,u_body) ->
                     let uu____68531 =
                       let uu____68534 =
                         let uu____68535 = is_monadic rc_opt1  in
                         if uu____68535 then M t else N t  in
                       comp_of_nm uu____68534  in
                     (uu____68531, s_body, u_body)
                  in
               (match uu____68468 with
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
                                 let uu____68575 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_68581  ->
                                           match uu___591_68581 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____68584 -> false))
                                    in
                                 if uu____68575
                                 then
                                   let uu____68587 =
                                     FStar_List.filter
                                       (fun uu___592_68591  ->
                                          match uu___592_68591 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____68594 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____68587
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____68605 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_68611  ->
                                         match uu___593_68611 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____68614 -> false))
                                  in
                               if uu____68605
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_68623  ->
                                        match uu___594_68623 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____68626 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____68628 =
                                   let uu____68629 =
                                     let uu____68634 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____68634
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____68629 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____68628
                               else
                                 (let uu____68641 =
                                    let uu___1432_68642 = rc  in
                                    let uu____68643 =
                                      let uu____68648 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____68648
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_68642.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____68643;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_68642.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____68641))
                       in
                    let uu____68653 =
                      let comp1 =
                        let uu____68661 = is_monadic rc_opt1  in
                        let uu____68663 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____68661 uu____68663
                         in
                      let uu____68664 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____68664,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____68653 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____68702 =
                             let uu____68703 =
                               let uu____68722 =
                                 let uu____68725 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____68725 s_rc_opt  in
                               (s_binders1, s_body1, uu____68722)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68703  in
                           mk1 uu____68702  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____68745 =
                             let uu____68746 =
                               let uu____68765 =
                                 let uu____68768 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____68768 u_rc_opt  in
                               (u_binders2, u_body2, uu____68765)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68746  in
                           mk1 uu____68745  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____68784;_};
            FStar_Syntax_Syntax.fv_delta = uu____68785;
            FStar_Syntax_Syntax.fv_qual = uu____68786;_}
          ->
          let uu____68789 =
            let uu____68794 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____68794  in
          (match uu____68789 with
           | (uu____68825,t) ->
               let uu____68827 =
                 let uu____68828 = normalize1 t  in N uu____68828  in
               (uu____68827, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____68829;
             FStar_Syntax_Syntax.vars = uu____68830;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____68909 = FStar_Syntax_Util.head_and_args e  in
          (match uu____68909 with
           | (unary_op1,uu____68933) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69004;
             FStar_Syntax_Syntax.vars = uu____69005;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____69101 = FStar_Syntax_Util.head_and_args e  in
          (match uu____69101 with
           | (unary_op1,uu____69125) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69204;
             FStar_Syntax_Syntax.vars = uu____69205;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____69243 = infer env a  in
          (match uu____69243 with
           | (t,s,u) ->
               let uu____69259 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69259 with
                | (head1,uu____69283) ->
                    let uu____69308 =
                      let uu____69309 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____69309  in
                    let uu____69310 =
                      let uu____69311 =
                        let uu____69312 =
                          let uu____69329 =
                            let uu____69340 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69340]  in
                          (head1, uu____69329)  in
                        FStar_Syntax_Syntax.Tm_app uu____69312  in
                      mk1 uu____69311  in
                    let uu____69377 =
                      let uu____69378 =
                        let uu____69379 =
                          let uu____69396 =
                            let uu____69407 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69407]  in
                          (head1, uu____69396)  in
                        FStar_Syntax_Syntax.Tm_app uu____69379  in
                      mk1 uu____69378  in
                    (uu____69308, uu____69310, uu____69377)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69444;
             FStar_Syntax_Syntax.vars = uu____69445;_},(a1,uu____69447)::a2::[])
          ->
          let uu____69503 = infer env a1  in
          (match uu____69503 with
           | (t,s,u) ->
               let uu____69519 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69519 with
                | (head1,uu____69543) ->
                    let uu____69568 =
                      let uu____69569 =
                        let uu____69570 =
                          let uu____69587 =
                            let uu____69598 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69598; a2]  in
                          (head1, uu____69587)  in
                        FStar_Syntax_Syntax.Tm_app uu____69570  in
                      mk1 uu____69569  in
                    let uu____69643 =
                      let uu____69644 =
                        let uu____69645 =
                          let uu____69662 =
                            let uu____69673 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69673; a2]  in
                          (head1, uu____69662)  in
                        FStar_Syntax_Syntax.Tm_app uu____69645  in
                      mk1 uu____69644  in
                    (t, uu____69568, uu____69643)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69718;
             FStar_Syntax_Syntax.vars = uu____69719;_},uu____69720)
          ->
          let uu____69745 =
            let uu____69751 =
              let uu____69753 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69753
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69751)  in
          FStar_Errors.raise_error uu____69745 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69763;
             FStar_Syntax_Syntax.vars = uu____69764;_},uu____69765)
          ->
          let uu____69790 =
            let uu____69796 =
              let uu____69798 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69798
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69796)  in
          FStar_Errors.raise_error uu____69790 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____69834 = check_n env head1  in
          (match uu____69834 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____69857 =
                   let uu____69858 = FStar_Syntax_Subst.compress t  in
                   uu____69858.FStar_Syntax_Syntax.n  in
                 match uu____69857 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____69862 -> true
                 | uu____69878 -> false  in
               let rec flatten1 t =
                 let uu____69900 =
                   let uu____69901 = FStar_Syntax_Subst.compress t  in
                   uu____69901.FStar_Syntax_Syntax.n  in
                 match uu____69900 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____69920);
                                FStar_Syntax_Syntax.pos = uu____69921;
                                FStar_Syntax_Syntax.vars = uu____69922;_})
                     when is_arrow t1 ->
                     let uu____69951 = flatten1 t1  in
                     (match uu____69951 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____70051,uu____70052) -> flatten1 e1
                 | uu____70093 ->
                     let uu____70094 =
                       let uu____70100 =
                         let uu____70102 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____70102
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____70100)  in
                     FStar_Errors.raise_err uu____70094
                  in
               let uu____70120 = flatten1 t_head  in
               (match uu____70120 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____70195 =
                          let uu____70201 =
                            let uu____70203 = FStar_Util.string_of_int n1  in
                            let uu____70205 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____70207 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____70203 uu____70205 uu____70207
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____70201)
                           in
                        FStar_Errors.raise_err uu____70195)
                     else ();
                     (let uu____70213 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____70213 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____70266 args1 =
                            match uu____70266 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____70366 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____70366
                                 | (binders3,[]) ->
                                     let uu____70404 =
                                       let uu____70405 =
                                         let uu____70408 =
                                           let uu____70409 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____70409
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____70408
                                          in
                                       uu____70405.FStar_Syntax_Syntax.n  in
                                     (match uu____70404 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____70442 =
                                            let uu____70443 =
                                              let uu____70444 =
                                                let uu____70459 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____70459)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____70444
                                               in
                                            mk1 uu____70443  in
                                          N uu____70442
                                      | uu____70472 -> failwith "wat?")
                                 | ([],uu____70474::uu____70475) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____70528)::binders3,(arg,uu____70531)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____70618 = FStar_List.splitAt n' binders1
                             in
                          (match uu____70618 with
                           | (binders2,uu____70652) ->
                               let uu____70685 =
                                 let uu____70708 =
                                   FStar_List.map2
                                     (fun uu____70770  ->
                                        fun uu____70771  ->
                                          match (uu____70770, uu____70771)
                                          with
                                          | ((bv,uu____70819),(arg,q)) ->
                                              let uu____70848 =
                                                let uu____70849 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____70849.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____70848 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____70870 ->
                                                   let uu____70871 =
                                                     let uu____70878 =
                                                       star_type' env arg  in
                                                     (uu____70878, q)  in
                                                   (uu____70871, [(arg, q)])
                                               | uu____70915 ->
                                                   let uu____70916 =
                                                     check_n env arg  in
                                                   (match uu____70916 with
                                                    | (uu____70941,s_arg,u_arg)
                                                        ->
                                                        let uu____70944 =
                                                          let uu____70953 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____70953
                                                          then
                                                            let uu____70964 =
                                                              let uu____70971
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____70971,
                                                                q)
                                                               in
                                                            [uu____70964;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____70944))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____70708  in
                               (match uu____70685 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____71099 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____71112 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____71099, uu____71112)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____71181) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____71187) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____71193,uu____71194) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____71236 =
            let uu____71237 = env.tc_const c  in N uu____71237  in
          (uu____71236, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____71244 ->
          let uu____71258 =
            let uu____71260 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____71260  in
          failwith uu____71258
      | FStar_Syntax_Syntax.Tm_type uu____71269 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____71277 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____71299 ->
          let uu____71306 =
            let uu____71308 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____71308  in
          failwith uu____71306
      | FStar_Syntax_Syntax.Tm_uvar uu____71317 ->
          let uu____71330 =
            let uu____71332 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____71332  in
          failwith uu____71330
      | FStar_Syntax_Syntax.Tm_delayed uu____71341 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71371 =
            let uu____71373 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____71373  in
          failwith uu____71371

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
          let uu____71422 = check_n env e0  in
          match uu____71422 with
          | (uu____71435,s_e0,u_e0) ->
              let uu____71438 =
                let uu____71467 =
                  FStar_List.map
                    (fun b  ->
                       let uu____71528 = FStar_Syntax_Subst.open_branch b  in
                       match uu____71528 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_71570 = env  in
                             let uu____71571 =
                               let uu____71572 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____71572
                                in
                             {
                               tcenv = uu____71571;
                               subst = (uu___1707_71570.subst);
                               tc_const = (uu___1707_71570.tc_const)
                             }  in
                           let uu____71575 = f env1 body  in
                           (match uu____71575 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____71647 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____71467  in
              (match uu____71438 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____71753 = FStar_List.hd nms  in
                     match uu____71753 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_71762  ->
                          match uu___595_71762 with
                          | M uu____71764 -> true
                          | uu____71766 -> false) nms
                      in
                   let uu____71768 =
                     let uu____71805 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____71895  ->
                              match uu____71895 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____72079 =
                                         check env original_body (M t2)  in
                                       (match uu____72079 with
                                        | (uu____72116,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____72155,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____71805  in
                   (match uu____71768 with
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
                              (fun uu____72344  ->
                                 match uu____72344 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____72395 =
                                         let uu____72396 =
                                           let uu____72413 =
                                             let uu____72424 =
                                               let uu____72433 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____72436 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____72433, uu____72436)  in
                                             [uu____72424]  in
                                           (s_body, uu____72413)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____72396
                                          in
                                       mk1 uu____72395  in
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
                            let uu____72571 =
                              let uu____72572 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____72572]  in
                            let uu____72591 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____72571 uu____72591
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____72615 =
                              let uu____72624 =
                                let uu____72631 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____72631
                                 in
                              [uu____72624]  in
                            let uu____72650 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____72615 uu____72650
                             in
                          let uu____72653 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____72692 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____72653, uu____72692)
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
                           let uu____72802 =
                             let uu____72803 =
                               let uu____72804 =
                                 let uu____72831 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____72831,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____72804
                                in
                             mk1 uu____72803  in
                           let uu____72890 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____72802, uu____72890))))

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
              let uu____72955 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____72955]  in
            let uu____72974 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____72974 with
            | (x_binders1,e21) ->
                let uu____72987 = infer env e1  in
                (match uu____72987 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____73004 = is_C t1  in
                       if uu____73004
                       then
                         let uu___1793_73007 = binding  in
                         let uu____73008 =
                           let uu____73011 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____73011  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_73007.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_73007.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____73008;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_73007.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_73007.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_73007.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_73007.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_73015 = env  in
                       let uu____73016 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_73018 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_73018.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_73018.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73016;
                         subst = (uu___1796_73015.subst);
                         tc_const = (uu___1796_73015.tc_const)
                       }  in
                     let uu____73019 = proceed env1 e21  in
                     (match uu____73019 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_73036 = binding  in
                            let uu____73037 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_73036.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_73036.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____73037;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_73036.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_73036.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_73036.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_73036.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____73040 =
                            let uu____73041 =
                              let uu____73042 =
                                let uu____73056 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_73073 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_73073.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_73073.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_73073.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_73073.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_73073.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_73073.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73056)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73042  in
                            mk1 uu____73041  in
                          let uu____73074 =
                            let uu____73075 =
                              let uu____73076 =
                                let uu____73090 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_73107 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_73107.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_73107.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_73107.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_73107.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_73107.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_73107.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73090)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73076  in
                            mk1 uu____73075  in
                          (nm_rec, uu____73040, uu____73074))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_73112 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_73112.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_73112.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_73112.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_73112.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_73112.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_73114 = env  in
                       let uu____73115 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_73117 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_73117.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_73117.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73115;
                         subst = (uu___1820_73114.subst);
                         tc_const = (uu___1820_73114.tc_const)
                       }  in
                     let uu____73118 = ensure_m env1 e21  in
                     (match uu____73118 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____73142 =
                              let uu____73143 =
                                let uu____73160 =
                                  let uu____73171 =
                                    let uu____73180 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____73183 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____73180, uu____73183)  in
                                  [uu____73171]  in
                                (s_e2, uu____73160)  in
                              FStar_Syntax_Syntax.Tm_app uu____73143  in
                            mk1 uu____73142  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____73225 =
                              let uu____73226 =
                                let uu____73243 =
                                  let uu____73254 =
                                    let uu____73263 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____73263)  in
                                  [uu____73254]  in
                                (s_e1, uu____73243)  in
                              FStar_Syntax_Syntax.Tm_app uu____73226  in
                            mk1 uu____73225  in
                          let uu____73299 =
                            let uu____73300 =
                              let uu____73301 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____73301]  in
                            FStar_Syntax_Util.abs uu____73300 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____73320 =
                            let uu____73321 =
                              let uu____73322 =
                                let uu____73336 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_73353 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_73353.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_73353.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_73353.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_73353.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_73353.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_73353.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73336)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73322  in
                            mk1 uu____73321  in
                          ((M t2), uu____73299, uu____73320)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73363 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____73363  in
      let uu____73364 = check env e mn  in
      match uu____73364 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73380 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73403 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____73403  in
      let uu____73404 = check env e mn  in
      match uu____73404 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73420 -> failwith "[check_m]: impossible"

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
        (let uu____73453 =
           let uu____73455 = is_C c  in Prims.op_Negation uu____73455  in
         if uu____73453 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____73469 =
           let uu____73470 = FStar_Syntax_Subst.compress c  in
           uu____73470.FStar_Syntax_Syntax.n  in
         match uu____73469 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____73499 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____73499 with
              | (wp_head,wp_args) ->
                  ((let uu____73543 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____73562 =
                           let uu____73564 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____73564
                            in
                         Prims.op_Negation uu____73562)
                       in
                    if uu____73543 then failwith "mismatch" else ());
                   (let uu____73577 =
                      let uu____73578 =
                        let uu____73595 =
                          FStar_List.map2
                            (fun uu____73633  ->
                               fun uu____73634  ->
                                 match (uu____73633, uu____73634) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____73696 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____73696
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____73705 =
                                         let uu____73707 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____73707 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____73705
                                       then
                                         let uu____73709 =
                                           let uu____73715 =
                                             let uu____73717 =
                                               print_implicit q  in
                                             let uu____73719 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____73717 uu____73719
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____73715)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____73709
                                       else ());
                                      (let uu____73725 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____73725, q)))) args wp_args
                           in
                        (head1, uu____73595)  in
                      FStar_Syntax_Syntax.Tm_app uu____73578  in
                    mk1 uu____73577)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____73771 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____73771 with
              | (binders_orig,comp1) ->
                  let uu____73778 =
                    let uu____73795 =
                      FStar_List.map
                        (fun uu____73835  ->
                           match uu____73835 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____73863 = is_C h  in
                               if uu____73863
                               then
                                 let w' =
                                   let uu____73879 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____73879
                                    in
                                 let uu____73881 =
                                   let uu____73890 =
                                     let uu____73899 =
                                       let uu____73906 =
                                         let uu____73907 =
                                           let uu____73908 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____73908  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____73907
                                          in
                                       (uu____73906, q)  in
                                     [uu____73899]  in
                                   (w', q) :: uu____73890  in
                                 (w', uu____73881)
                               else
                                 (let x =
                                    let uu____73942 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____73942
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____73795  in
                  (match uu____73778 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____74016 =
                           let uu____74019 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____74019
                            in
                         FStar_Syntax_Subst.subst_comp uu____74016 comp1  in
                       let app =
                         let uu____74023 =
                           let uu____74024 =
                             let uu____74041 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____74060 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____74061 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____74060, uu____74061)) bvs
                                in
                             (wp, uu____74041)  in
                           FStar_Syntax_Syntax.Tm_app uu____74024  in
                         mk1 uu____74023  in
                       let comp3 =
                         let uu____74076 = type_of_comp comp2  in
                         let uu____74077 = is_monadic_comp comp2  in
                         trans_G env uu____74076 uu____74077 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____74080,uu____74081) ->
             trans_F_ env e wp
         | uu____74122 -> failwith "impossible trans_F_")

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
            let uu____74130 =
              let uu____74131 = star_type' env h  in
              let uu____74134 =
                let uu____74145 =
                  let uu____74154 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____74154)  in
                [uu____74145]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____74131;
                FStar_Syntax_Syntax.effect_args = uu____74134;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____74130
          else
            (let uu____74180 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____74180)

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
    fun t  -> let uu____74201 = n env.tcenv t  in star_type' env uu____74201
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____74221 = n env.tcenv t  in check_n env uu____74221
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____74238 = n env.tcenv c  in
        let uu____74239 = n env.tcenv wp  in
        trans_F_ env uu____74238 uu____74239
  