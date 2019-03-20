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
              let uu___613_61022 = a  in
              let uu____61023 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_61022.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_61022.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____61023
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____61036 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____61036
             then
               (d "Elaborating extra WP combinators";
                (let uu____61042 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____61042))
             else ());
            (let rec collect_binders t =
               let uu____61061 =
                 let uu____61062 =
                   let uu____61065 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____61065
                    in
                 uu____61062.FStar_Syntax_Syntax.n  in
               match uu____61061 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____61100) -> t1
                     | uu____61109 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____61111 = collect_binders rest  in
                   FStar_List.append bs uu____61111
               | FStar_Syntax_Syntax.Tm_type uu____61126 -> []
               | uu____61133 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____61160 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____61160
                 FStar_Syntax_Util.name_binders
                in
             (let uu____61186 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____61186
              then
                let uu____61190 =
                  let uu____61192 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____61192  in
                d uu____61190
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____61230 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____61230 with
                | (sigelt,fv) ->
                    ((let uu____61238 =
                        let uu____61241 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____61241
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____61238);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____61321  ->
                     match uu____61321 with
                     | (t,b) ->
                         let uu____61335 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____61335))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____61374 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____61374))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____61408 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____61408)
                 in
              let uu____61411 =
                let uu____61428 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____61453 =
                        let uu____61456 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____61456  in
                      FStar_Syntax_Util.arrow gamma uu____61453  in
                    let uu____61457 =
                      let uu____61458 =
                        let uu____61467 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____61474 =
                          let uu____61483 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____61483]  in
                        uu____61467 :: uu____61474  in
                      FStar_List.append binders uu____61458  in
                    FStar_Syntax_Util.abs uu____61457 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____61514 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____61515 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____61514, uu____61515)  in
                match uu____61428 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____61557 =
                        let uu____61558 =
                          let uu____61575 =
                            let uu____61586 =
                              FStar_List.map
                                (fun uu____61608  ->
                                   match uu____61608 with
                                   | (bv,uu____61620) ->
                                       let uu____61625 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____61626 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____61625, uu____61626)) binders
                               in
                            let uu____61628 =
                              let uu____61635 =
                                let uu____61640 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____61641 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____61640, uu____61641)  in
                              let uu____61643 =
                                let uu____61650 =
                                  let uu____61655 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____61655)  in
                                [uu____61650]  in
                              uu____61635 :: uu____61643  in
                            FStar_List.append uu____61586 uu____61628  in
                          (fv, uu____61575)  in
                        FStar_Syntax_Syntax.Tm_app uu____61558  in
                      mk1 uu____61557  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____61411 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____61728 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____61728
                       in
                    let ret1 =
                      let uu____61733 =
                        let uu____61734 =
                          let uu____61737 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____61737  in
                        FStar_Syntax_Util.residual_tot uu____61734  in
                      FStar_Pervasives_Native.Some uu____61733  in
                    let body =
                      let uu____61741 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____61741 ret1  in
                    let uu____61744 =
                      let uu____61745 = mk_all_implicit binders  in
                      let uu____61752 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____61745 uu____61752  in
                    FStar_Syntax_Util.abs uu____61744 body ret1  in
                  let c_pure1 =
                    let uu____61790 = mk_lid "pure"  in
                    register env1 uu____61790 c_pure  in
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
                      let uu____61800 =
                        let uu____61801 =
                          let uu____61802 =
                            let uu____61811 =
                              let uu____61818 =
                                let uu____61819 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____61819
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____61818  in
                            [uu____61811]  in
                          let uu____61832 =
                            let uu____61835 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____61835  in
                          FStar_Syntax_Util.arrow uu____61802 uu____61832  in
                        mk_gctx uu____61801  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____61800
                       in
                    let r =
                      let uu____61838 =
                        let uu____61839 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____61839  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____61838
                       in
                    let ret1 =
                      let uu____61844 =
                        let uu____61845 =
                          let uu____61848 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____61848  in
                        FStar_Syntax_Util.residual_tot uu____61845  in
                      FStar_Pervasives_Native.Some uu____61844  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____61858 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____61861 =
                          let uu____61872 =
                            let uu____61875 =
                              let uu____61876 =
                                let uu____61877 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____61877
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____61876  in
                            [uu____61875]  in
                          FStar_List.append gamma_as_args uu____61872  in
                        FStar_Syntax_Util.mk_app uu____61858 uu____61861  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____61880 =
                      let uu____61881 = mk_all_implicit binders  in
                      let uu____61888 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____61881 uu____61888  in
                    FStar_Syntax_Util.abs uu____61880 outer_body ret1  in
                  let c_app1 =
                    let uu____61940 = mk_lid "app"  in
                    register env1 uu____61940 c_app  in
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
                      let uu____61952 =
                        let uu____61961 =
                          let uu____61968 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____61968  in
                        [uu____61961]  in
                      let uu____61981 =
                        let uu____61984 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____61984  in
                      FStar_Syntax_Util.arrow uu____61952 uu____61981  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____61988 =
                        let uu____61989 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____61989  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____61988
                       in
                    let ret1 =
                      let uu____61994 =
                        let uu____61995 =
                          let uu____61998 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____61998  in
                        FStar_Syntax_Util.residual_tot uu____61995  in
                      FStar_Pervasives_Native.Some uu____61994  in
                    let uu____61999 =
                      let uu____62000 = mk_all_implicit binders  in
                      let uu____62007 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____62000 uu____62007  in
                    let uu____62058 =
                      let uu____62061 =
                        let uu____62072 =
                          let uu____62075 =
                            let uu____62076 =
                              let uu____62087 =
                                let uu____62090 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____62090]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62087
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62076  in
                          let uu____62099 =
                            let uu____62102 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____62102]  in
                          uu____62075 :: uu____62099  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62072
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62061  in
                    FStar_Syntax_Util.abs uu____61999 uu____62058 ret1  in
                  let c_lift11 =
                    let uu____62112 = mk_lid "lift1"  in
                    register env1 uu____62112 c_lift1  in
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
                      let uu____62126 =
                        let uu____62135 =
                          let uu____62142 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62142  in
                        let uu____62143 =
                          let uu____62152 =
                            let uu____62159 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____62159  in
                          [uu____62152]  in
                        uu____62135 :: uu____62143  in
                      let uu____62178 =
                        let uu____62181 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62181  in
                      FStar_Syntax_Util.arrow uu____62126 uu____62178  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62185 =
                        let uu____62186 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62186  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62185
                       in
                    let a2 =
                      let uu____62189 =
                        let uu____62190 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____62190  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____62189
                       in
                    let ret1 =
                      let uu____62195 =
                        let uu____62196 =
                          let uu____62199 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____62199  in
                        FStar_Syntax_Util.residual_tot uu____62196  in
                      FStar_Pervasives_Native.Some uu____62195  in
                    let uu____62200 =
                      let uu____62201 = mk_all_implicit binders  in
                      let uu____62208 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____62201 uu____62208  in
                    let uu____62273 =
                      let uu____62276 =
                        let uu____62287 =
                          let uu____62290 =
                            let uu____62291 =
                              let uu____62302 =
                                let uu____62305 =
                                  let uu____62306 =
                                    let uu____62317 =
                                      let uu____62320 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____62320]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____62317
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____62306
                                   in
                                let uu____62329 =
                                  let uu____62332 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____62332]  in
                                uu____62305 :: uu____62329  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62302
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____62291  in
                          let uu____62341 =
                            let uu____62344 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____62344]  in
                          uu____62290 :: uu____62341  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62287
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62276  in
                    FStar_Syntax_Util.abs uu____62200 uu____62273 ret1  in
                  let c_lift21 =
                    let uu____62354 = mk_lid "lift2"  in
                    register env1 uu____62354 c_lift2  in
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
                      let uu____62366 =
                        let uu____62375 =
                          let uu____62382 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62382  in
                        [uu____62375]  in
                      let uu____62395 =
                        let uu____62398 =
                          let uu____62399 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62399  in
                        FStar_Syntax_Syntax.mk_Total uu____62398  in
                      FStar_Syntax_Util.arrow uu____62366 uu____62395  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____62405 =
                        let uu____62406 =
                          let uu____62409 =
                            let uu____62410 =
                              let uu____62419 =
                                let uu____62426 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____62426
                                 in
                              [uu____62419]  in
                            let uu____62439 =
                              let uu____62442 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____62442  in
                            FStar_Syntax_Util.arrow uu____62410 uu____62439
                             in
                          mk_ctx uu____62409  in
                        FStar_Syntax_Util.residual_tot uu____62406  in
                      FStar_Pervasives_Native.Some uu____62405  in
                    let e1 =
                      let uu____62444 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____62444
                       in
                    let body =
                      let uu____62449 =
                        let uu____62450 =
                          let uu____62459 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____62459]  in
                        FStar_List.append gamma uu____62450  in
                      let uu____62484 =
                        let uu____62487 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____62490 =
                          let uu____62501 =
                            let uu____62502 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____62502  in
                          let uu____62503 = args_of_binders1 gamma  in
                          uu____62501 :: uu____62503  in
                        FStar_Syntax_Util.mk_app uu____62487 uu____62490  in
                      FStar_Syntax_Util.abs uu____62449 uu____62484 ret1  in
                    let uu____62506 =
                      let uu____62507 = mk_all_implicit binders  in
                      let uu____62514 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____62507 uu____62514  in
                    FStar_Syntax_Util.abs uu____62506 body ret1  in
                  let c_push1 =
                    let uu____62559 = mk_lid "push"  in
                    register env1 uu____62559 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____62586 =
                        let uu____62587 =
                          let uu____62604 = args_of_binders1 binders  in
                          (c, uu____62604)  in
                        FStar_Syntax_Syntax.Tm_app uu____62587  in
                      mk1 uu____62586
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____62633 =
                        let uu____62634 =
                          let uu____62643 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____62650 =
                            let uu____62659 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____62659]  in
                          uu____62643 :: uu____62650  in
                        let uu____62684 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____62634 uu____62684  in
                      FStar_Syntax_Syntax.mk_Total uu____62633  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____62689 =
                      let uu____62690 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____62690  in
                    let uu____62705 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____62710 =
                        let uu____62713 =
                          let uu____62724 =
                            let uu____62727 =
                              let uu____62728 =
                                let uu____62739 =
                                  let uu____62748 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____62748  in
                                [uu____62739]  in
                              FStar_Syntax_Util.mk_app l_ite uu____62728  in
                            [uu____62727]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____62724
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____62713  in
                      FStar_Syntax_Util.ascribe uu____62710
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____62689 uu____62705
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____62792 = mk_lid "wp_if_then_else"  in
                    register env1 uu____62792 wp_if_then_else  in
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
                      let uu____62809 =
                        let uu____62820 =
                          let uu____62823 =
                            let uu____62824 =
                              let uu____62835 =
                                let uu____62838 =
                                  let uu____62839 =
                                    let uu____62850 =
                                      let uu____62859 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62859
                                       in
                                    [uu____62850]  in
                                  FStar_Syntax_Util.mk_app l_and uu____62839
                                   in
                                [uu____62838]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62835
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62824  in
                          let uu____62884 =
                            let uu____62887 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____62887]  in
                          uu____62823 :: uu____62884  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62820
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62809  in
                    let uu____62896 =
                      let uu____62897 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____62897  in
                    FStar_Syntax_Util.abs uu____62896 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____62913 = mk_lid "wp_assert"  in
                    register env1 uu____62913 wp_assert  in
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
                      let uu____62930 =
                        let uu____62941 =
                          let uu____62944 =
                            let uu____62945 =
                              let uu____62956 =
                                let uu____62959 =
                                  let uu____62960 =
                                    let uu____62971 =
                                      let uu____62980 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62980
                                       in
                                    [uu____62971]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____62960
                                   in
                                [uu____62959]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62956
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62945  in
                          let uu____63005 =
                            let uu____63008 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____63008]  in
                          uu____62944 :: uu____63005  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62941
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62930  in
                    let uu____63017 =
                      let uu____63018 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____63018  in
                    FStar_Syntax_Util.abs uu____63017 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____63034 = mk_lid "wp_assume"  in
                    register env1 uu____63034 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____63047 =
                        let uu____63056 =
                          let uu____63063 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____63063  in
                        [uu____63056]  in
                      let uu____63076 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____63047 uu____63076  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____63084 =
                        let uu____63095 =
                          let uu____63098 =
                            let uu____63099 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____63099  in
                          let uu____63118 =
                            let uu____63121 =
                              let uu____63122 =
                                let uu____63133 =
                                  let uu____63136 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____63136]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____63133
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____63122
                               in
                            [uu____63121]  in
                          uu____63098 :: uu____63118  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63095
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63084  in
                    let uu____63153 =
                      let uu____63154 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____63154  in
                    FStar_Syntax_Util.abs uu____63153 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____63170 = mk_lid "wp_close"  in
                    register env1 uu____63170 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____63181 =
                      let uu____63182 =
                        let uu____63183 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____63183
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____63182
                       in
                    FStar_Pervasives_Native.Some uu____63181  in
                  let mk_forall1 x body =
                    let uu____63195 =
                      let uu____63202 =
                        let uu____63203 =
                          let uu____63220 =
                            let uu____63231 =
                              let uu____63240 =
                                let uu____63241 =
                                  let uu____63242 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____63242]  in
                                FStar_Syntax_Util.abs uu____63241 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____63240  in
                            [uu____63231]  in
                          (FStar_Syntax_Util.tforall, uu____63220)  in
                        FStar_Syntax_Syntax.Tm_app uu____63203  in
                      FStar_Syntax_Syntax.mk uu____63202  in
                    uu____63195 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____63300 =
                      let uu____63301 = FStar_Syntax_Subst.compress t  in
                      uu____63301.FStar_Syntax_Syntax.n  in
                    match uu____63300 with
                    | FStar_Syntax_Syntax.Tm_type uu____63305 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63338  ->
                              match uu____63338 with
                              | (b,uu____63347) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____63352 -> true  in
                  let rec is_monotonic t =
                    let uu____63365 =
                      let uu____63366 = FStar_Syntax_Subst.compress t  in
                      uu____63366.FStar_Syntax_Syntax.n  in
                    match uu____63365 with
                    | FStar_Syntax_Syntax.Tm_type uu____63370 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63403  ->
                              match uu____63403 with
                              | (b,uu____63412) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____63417 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____63491 =
                      let uu____63492 = FStar_Syntax_Subst.compress t1  in
                      uu____63492.FStar_Syntax_Syntax.n  in
                    match uu____63491 with
                    | FStar_Syntax_Syntax.Tm_type uu____63497 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____63500);
                                      FStar_Syntax_Syntax.pos = uu____63501;
                                      FStar_Syntax_Syntax.vars = uu____63502;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63546 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63546
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63556 =
                              let uu____63559 =
                                let uu____63570 =
                                  let uu____63579 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63579  in
                                [uu____63570]  in
                              FStar_Syntax_Util.mk_app x uu____63559  in
                            let uu____63596 =
                              let uu____63599 =
                                let uu____63610 =
                                  let uu____63619 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63619  in
                                [uu____63610]  in
                              FStar_Syntax_Util.mk_app y uu____63599  in
                            mk_rel1 b uu____63556 uu____63596  in
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
                             let uu____63643 =
                               let uu____63646 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63649 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63646 uu____63649  in
                             let uu____63652 =
                               let uu____63655 =
                                 let uu____63658 =
                                   let uu____63669 =
                                     let uu____63678 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63678
                                      in
                                   [uu____63669]  in
                                 FStar_Syntax_Util.mk_app x uu____63658  in
                               let uu____63695 =
                                 let uu____63698 =
                                   let uu____63709 =
                                     let uu____63718 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63718
                                      in
                                   [uu____63709]  in
                                 FStar_Syntax_Util.mk_app y uu____63698  in
                               mk_rel1 b uu____63655 uu____63695  in
                             FStar_Syntax_Util.mk_imp uu____63643 uu____63652
                              in
                           let uu____63735 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63735)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____63738);
                                      FStar_Syntax_Syntax.pos = uu____63739;
                                      FStar_Syntax_Syntax.vars = uu____63740;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63784 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63784
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63794 =
                              let uu____63797 =
                                let uu____63808 =
                                  let uu____63817 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63817  in
                                [uu____63808]  in
                              FStar_Syntax_Util.mk_app x uu____63797  in
                            let uu____63834 =
                              let uu____63837 =
                                let uu____63848 =
                                  let uu____63857 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63857  in
                                [uu____63848]  in
                              FStar_Syntax_Util.mk_app y uu____63837  in
                            mk_rel1 b uu____63794 uu____63834  in
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
                             let uu____63881 =
                               let uu____63884 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63887 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63884 uu____63887  in
                             let uu____63890 =
                               let uu____63893 =
                                 let uu____63896 =
                                   let uu____63907 =
                                     let uu____63916 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63916
                                      in
                                   [uu____63907]  in
                                 FStar_Syntax_Util.mk_app x uu____63896  in
                               let uu____63933 =
                                 let uu____63936 =
                                   let uu____63947 =
                                     let uu____63956 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63956
                                      in
                                   [uu____63947]  in
                                 FStar_Syntax_Util.mk_app y uu____63936  in
                               mk_rel1 b uu____63893 uu____63933  in
                             FStar_Syntax_Util.mk_imp uu____63881 uu____63890
                              in
                           let uu____63973 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63973)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_64012 = t1  in
                          let uu____64013 =
                            let uu____64014 =
                              let uu____64029 =
                                let uu____64032 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____64032  in
                              ([binder], uu____64029)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____64014  in
                          {
                            FStar_Syntax_Syntax.n = uu____64013;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_64012.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_64012.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____64055 ->
                        failwith "unhandled arrow"
                    | uu____64073 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____64110 =
                        let uu____64111 = FStar_Syntax_Subst.compress t1  in
                        uu____64111.FStar_Syntax_Syntax.n  in
                      match uu____64110 with
                      | FStar_Syntax_Syntax.Tm_type uu____64114 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____64141 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____64141
                          ->
                          let project i tuple =
                            let projector =
                              let uu____64162 =
                                let uu____64163 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____64163 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____64162
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____64193 =
                            let uu____64204 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____64222  ->
                                     match uu____64222 with
                                     | (t2,q) ->
                                         let uu____64242 = project i x  in
                                         let uu____64245 = project i y  in
                                         mk_stronger t2 uu____64242
                                           uu____64245) args
                               in
                            match uu____64204 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____64193 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____64299);
                                      FStar_Syntax_Syntax.pos = uu____64300;
                                      FStar_Syntax_Syntax.vars = uu____64301;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64345  ->
                                   match uu____64345 with
                                   | (bv,q) ->
                                       let uu____64359 =
                                         let uu____64361 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64361  in
                                       FStar_Syntax_Syntax.gen_bv uu____64359
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64370 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64370) bvs
                             in
                          let body =
                            let uu____64372 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64375 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64372 uu____64375  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____64384);
                                      FStar_Syntax_Syntax.pos = uu____64385;
                                      FStar_Syntax_Syntax.vars = uu____64386;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64430  ->
                                   match uu____64430 with
                                   | (bv,q) ->
                                       let uu____64444 =
                                         let uu____64446 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64446  in
                                       FStar_Syntax_Syntax.gen_bv uu____64444
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64455 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64455) bvs
                             in
                          let body =
                            let uu____64457 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64460 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64457 uu____64460  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____64467 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____64470 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____64473 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____64476 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____64470 uu____64473 uu____64476  in
                    let uu____64479 =
                      let uu____64480 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____64480  in
                    FStar_Syntax_Util.abs uu____64479 body ret_tot_type  in
                  let stronger1 =
                    let uu____64522 = mk_lid "stronger"  in
                    register env1 uu____64522 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64530 = FStar_Util.prefix gamma  in
                    match uu____64530 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____64596 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____64596
                             in
                          let uu____64601 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____64601 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____64611 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____64611  in
                              let guard_free1 =
                                let uu____64623 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____64623  in
                              let pat =
                                let uu____64627 =
                                  let uu____64638 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____64638]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____64627
                                 in
                              let pattern_guarded_body =
                                let uu____64666 =
                                  let uu____64667 =
                                    let uu____64674 =
                                      let uu____64675 =
                                        let uu____64688 =
                                          let uu____64699 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____64699]  in
                                        [uu____64688]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____64675
                                       in
                                    (body, uu____64674)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____64667  in
                                mk1 uu____64666  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____64746 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____64755 =
                            let uu____64758 =
                              let uu____64759 =
                                let uu____64762 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____64765 =
                                  let uu____64776 = args_of_binders1 wp_args
                                     in
                                  let uu____64779 =
                                    let uu____64782 =
                                      let uu____64783 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____64783
                                       in
                                    [uu____64782]  in
                                  FStar_List.append uu____64776 uu____64779
                                   in
                                FStar_Syntax_Util.mk_app uu____64762
                                  uu____64765
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____64759  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____64758
                             in
                          FStar_Syntax_Util.abs gamma uu____64755
                            ret_gtot_type
                           in
                        let uu____64784 =
                          let uu____64785 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____64785  in
                        FStar_Syntax_Util.abs uu____64784 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____64801 = mk_lid "ite_wp"  in
                    register env1 uu____64801 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64809 = FStar_Util.prefix gamma  in
                    match uu____64809 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____64867 =
                            let uu____64868 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____64875 =
                              let uu____64886 =
                                let uu____64895 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____64895  in
                              [uu____64886]  in
                            FStar_Syntax_Util.mk_app uu____64868 uu____64875
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____64867
                           in
                        let uu____64912 =
                          let uu____64913 =
                            let uu____64922 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____64922 gamma  in
                          FStar_List.append binders uu____64913  in
                        FStar_Syntax_Util.abs uu____64912 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____64944 = mk_lid "null_wp"  in
                    register env1 uu____64944 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____64957 =
                        let uu____64968 =
                          let uu____64971 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____64972 =
                            let uu____64975 =
                              let uu____64976 =
                                let uu____64987 =
                                  let uu____64996 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____64996  in
                                [uu____64987]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____64976
                               in
                            let uu____65013 =
                              let uu____65016 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____65016]  in
                            uu____64975 :: uu____65013  in
                          uu____64971 :: uu____64972  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____64968
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____64957  in
                    let uu____65025 =
                      let uu____65026 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____65026  in
                    FStar_Syntax_Util.abs uu____65025 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____65042 = mk_lid "wp_trivial"  in
                    register env1 uu____65042 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____65048 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____65048
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____65060 =
                      let uu____65061 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____65061  in
                    let uu____65087 =
                      let uu___934_65088 = ed  in
                      let uu____65089 =
                        let uu____65090 = c wp_if_then_else2  in
                        ([], uu____65090)  in
                      let uu____65097 =
                        let uu____65098 = c ite_wp2  in ([], uu____65098)  in
                      let uu____65105 =
                        let uu____65106 = c stronger2  in ([], uu____65106)
                         in
                      let uu____65113 =
                        let uu____65114 = c wp_close2  in ([], uu____65114)
                         in
                      let uu____65121 =
                        let uu____65122 = c wp_assert2  in ([], uu____65122)
                         in
                      let uu____65129 =
                        let uu____65130 = c wp_assume2  in ([], uu____65130)
                         in
                      let uu____65137 =
                        let uu____65138 = c null_wp2  in ([], uu____65138)
                         in
                      let uu____65145 =
                        let uu____65146 = c wp_trivial2  in ([], uu____65146)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_65088.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_65088.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_65088.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_65088.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_65088.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_65088.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_65088.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____65089;
                        FStar_Syntax_Syntax.ite_wp = uu____65097;
                        FStar_Syntax_Syntax.stronger = uu____65105;
                        FStar_Syntax_Syntax.close_wp = uu____65113;
                        FStar_Syntax_Syntax.assert_p = uu____65121;
                        FStar_Syntax_Syntax.assume_p = uu____65129;
                        FStar_Syntax_Syntax.null_wp = uu____65137;
                        FStar_Syntax_Syntax.trivial = uu____65145;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_65088.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_65088.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_65088.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_65088.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_65088.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____65060, uu____65087)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_65170 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_65170.subst);
        tc_const = (uu___939_65170.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____65191 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____65210 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65230) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_65244  ->
                match uu___585_65244 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____65247 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____65249 ->
        let uu____65250 =
          let uu____65256 =
            let uu____65258 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____65258
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____65256)  in
        FStar_Errors.raise_error uu____65250 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_65268  ->
    match uu___586_65268 with
    | N t ->
        let uu____65271 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____65271
    | M t ->
        let uu____65275 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____65275
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____65284,c) -> nm_of_comp c
    | uu____65306 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____65319 = nm_of_comp c  in
    match uu____65319 with | M uu____65321 -> true | N uu____65323 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____65334 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____65350 =
        let uu____65359 =
          let uu____65366 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____65366  in
        [uu____65359]  in
      let uu____65385 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____65350 uu____65385  in
    let uu____65388 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____65388
  
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
        let uu____65430 =
          let uu____65431 =
            let uu____65446 =
              let uu____65455 =
                let uu____65462 =
                  let uu____65463 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____65463  in
                let uu____65464 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____65462, uu____65464)  in
              [uu____65455]  in
            let uu____65482 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____65446, uu____65482)  in
          FStar_Syntax_Syntax.Tm_arrow uu____65431  in
        mk1 uu____65430

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____65522) ->
          let binders1 =
            FStar_List.map
              (fun uu____65568  ->
                 match uu____65568 with
                 | (bv,aqual) ->
                     let uu____65587 =
                       let uu___989_65588 = bv  in
                       let uu____65589 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_65588.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_65588.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____65589
                       }  in
                     (uu____65587, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____65594,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____65596);
                              FStar_Syntax_Syntax.pos = uu____65597;
                              FStar_Syntax_Syntax.vars = uu____65598;_})
               ->
               let uu____65627 =
                 let uu____65628 =
                   let uu____65643 =
                     let uu____65646 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____65646  in
                   (binders1, uu____65643)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____65628  in
               mk1 uu____65627
           | uu____65657 ->
               let uu____65658 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____65658 with
                | N hn ->
                    let uu____65660 =
                      let uu____65661 =
                        let uu____65676 =
                          let uu____65679 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____65679  in
                        (binders1, uu____65676)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65661  in
                    mk1 uu____65660
                | M a ->
                    let uu____65691 =
                      let uu____65692 =
                        let uu____65707 =
                          let uu____65716 =
                            let uu____65725 =
                              let uu____65732 =
                                let uu____65733 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____65733  in
                              let uu____65734 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____65732, uu____65734)  in
                            [uu____65725]  in
                          FStar_List.append binders1 uu____65716  in
                        let uu____65758 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____65707, uu____65758)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65692  in
                    mk1 uu____65691))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____65852 = f x  in
                    FStar_Util.string_builder_append strb uu____65852);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____65861 = f x1  in
                         FStar_Util.string_builder_append strb uu____65861))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____65865 =
              let uu____65871 =
                let uu____65873 = FStar_Syntax_Print.term_to_string t2  in
                let uu____65875 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____65873 uu____65875
                 in
              (FStar_Errors.Warning_DependencyFound, uu____65871)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____65865  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____65897 =
              let uu____65898 = FStar_Syntax_Subst.compress ty  in
              uu____65898.FStar_Syntax_Syntax.n  in
            match uu____65897 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____65924 =
                  let uu____65926 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____65926  in
                if uu____65924
                then false
                else
                  (try
                     (fun uu___1038_65943  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____65967 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____65967 s  in
                              let uu____65970 =
                                let uu____65972 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____65972  in
                              if uu____65970
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____65978 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____65978 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____66003  ->
                                          match uu____66003 with
                                          | (bv,uu____66015) ->
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
            | uu____66043 ->
                ((let uu____66045 =
                    let uu____66051 =
                      let uu____66053 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____66053
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____66051)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____66045);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____66069 =
              let uu____66070 = FStar_Syntax_Subst.compress head2  in
              uu____66070.FStar_Syntax_Syntax.n  in
            match uu____66069 with
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
                  (let uu____66076 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____66076)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____66079 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____66079 with
                 | ((uu____66089,ty),uu____66091) ->
                     let uu____66096 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____66096
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____66109 =
                         let uu____66110 = FStar_Syntax_Subst.compress res
                            in
                         uu____66110.FStar_Syntax_Syntax.n  in
                       (match uu____66109 with
                        | FStar_Syntax_Syntax.Tm_app uu____66114 -> true
                        | uu____66132 ->
                            ((let uu____66134 =
                                let uu____66140 =
                                  let uu____66142 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____66142
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____66140)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____66134);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____66150 -> true
            | FStar_Syntax_Syntax.Tm_name uu____66152 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____66155) ->
                is_valid_application t2
            | uu____66160 -> false  in
          let uu____66162 = is_valid_application head1  in
          if uu____66162
          then
            let uu____66165 =
              let uu____66166 =
                let uu____66183 =
                  FStar_List.map
                    (fun uu____66212  ->
                       match uu____66212 with
                       | (t2,qual) ->
                           let uu____66237 = star_type' env t2  in
                           (uu____66237, qual)) args
                   in
                (head1, uu____66183)  in
              FStar_Syntax_Syntax.Tm_app uu____66166  in
            mk1 uu____66165
          else
            (let uu____66254 =
               let uu____66260 =
                 let uu____66262 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____66262
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____66260)  in
             FStar_Errors.raise_err uu____66254)
      | FStar_Syntax_Syntax.Tm_bvar uu____66266 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____66267 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____66268 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____66269 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____66297 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____66297 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_66305 = env  in
                 let uu____66306 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____66306;
                   subst = (uu___1110_66305.subst);
                   tc_const = (uu___1110_66305.tc_const)
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
               ((let uu___1125_66333 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_66333.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_66333.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____66340 =
            let uu____66341 =
              let uu____66348 = star_type' env t2  in (uu____66348, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____66341  in
          mk1 uu____66340
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____66400 =
            let uu____66401 =
              let uu____66428 = star_type' env e  in
              let uu____66431 =
                let uu____66448 =
                  let uu____66457 = star_type' env t2  in
                  FStar_Util.Inl uu____66457  in
                (uu____66448, FStar_Pervasives_Native.None)  in
              (uu____66428, uu____66431, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66401  in
          mk1 uu____66400
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____66545 =
            let uu____66546 =
              let uu____66573 = star_type' env e  in
              let uu____66576 =
                let uu____66593 =
                  let uu____66602 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____66602  in
                (uu____66593, FStar_Pervasives_Native.None)  in
              (uu____66573, uu____66576, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66546  in
          mk1 uu____66545
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____66643,(uu____66644,FStar_Pervasives_Native.Some uu____66645),uu____66646)
          ->
          let uu____66695 =
            let uu____66701 =
              let uu____66703 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____66703
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66701)  in
          FStar_Errors.raise_err uu____66695
      | FStar_Syntax_Syntax.Tm_refine uu____66707 ->
          let uu____66714 =
            let uu____66720 =
              let uu____66722 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____66722
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66720)  in
          FStar_Errors.raise_err uu____66714
      | FStar_Syntax_Syntax.Tm_uinst uu____66726 ->
          let uu____66733 =
            let uu____66739 =
              let uu____66741 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____66741
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66739)  in
          FStar_Errors.raise_err uu____66733
      | FStar_Syntax_Syntax.Tm_quoted uu____66745 ->
          let uu____66752 =
            let uu____66758 =
              let uu____66760 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____66760
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66758)  in
          FStar_Errors.raise_err uu____66752
      | FStar_Syntax_Syntax.Tm_constant uu____66764 ->
          let uu____66765 =
            let uu____66771 =
              let uu____66773 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____66773
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66771)  in
          FStar_Errors.raise_err uu____66765
      | FStar_Syntax_Syntax.Tm_match uu____66777 ->
          let uu____66800 =
            let uu____66806 =
              let uu____66808 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____66808
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66806)  in
          FStar_Errors.raise_err uu____66800
      | FStar_Syntax_Syntax.Tm_let uu____66812 ->
          let uu____66826 =
            let uu____66832 =
              let uu____66834 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____66834
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66832)  in
          FStar_Errors.raise_err uu____66826
      | FStar_Syntax_Syntax.Tm_uvar uu____66838 ->
          let uu____66851 =
            let uu____66857 =
              let uu____66859 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____66859
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66857)  in
          FStar_Errors.raise_err uu____66851
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____66863 =
            let uu____66869 =
              let uu____66871 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____66871
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66869)  in
          FStar_Errors.raise_err uu____66863
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66876 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____66876
      | FStar_Syntax_Syntax.Tm_delayed uu____66879 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_66911  ->
    match uu___588_66911 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_66922  ->
                match uu___587_66922 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____66925 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____66935 =
      let uu____66936 = FStar_Syntax_Subst.compress t  in
      uu____66936.FStar_Syntax_Syntax.n  in
    match uu____66935 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____66968 =
            let uu____66969 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____66969  in
          is_C uu____66968  in
        if r
        then
          ((let uu____66993 =
              let uu____66995 =
                FStar_List.for_all
                  (fun uu____67006  ->
                     match uu____67006 with | (h,uu____67015) -> is_C h) args
                 in
              Prims.op_Negation uu____66995  in
            if uu____66993 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____67028 =
              let uu____67030 =
                FStar_List.for_all
                  (fun uu____67042  ->
                     match uu____67042 with
                     | (h,uu____67051) ->
                         let uu____67056 = is_C h  in
                         Prims.op_Negation uu____67056) args
                 in
              Prims.op_Negation uu____67030  in
            if uu____67028 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____67085 = nm_of_comp comp  in
        (match uu____67085 with
         | M t1 ->
             ((let uu____67089 = is_C t1  in
               if uu____67089 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____67098) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____67104) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____67110,uu____67111) -> is_C t1
    | uu____67152 -> false
  
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
          let uu____67188 =
            let uu____67189 =
              let uu____67206 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____67209 =
                let uu____67220 =
                  let uu____67229 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____67229)  in
                [uu____67220]  in
              (uu____67206, uu____67209)  in
            FStar_Syntax_Syntax.Tm_app uu____67189  in
          mk1 uu____67188  in
        let uu____67265 =
          let uu____67266 = FStar_Syntax_Syntax.mk_binder p  in [uu____67266]
           in
        FStar_Syntax_Util.abs uu____67265 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_67291  ->
    match uu___589_67291 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____67294 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____67532 =
          match uu____67532 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____67569 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____67572 =
                       let uu____67574 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____67574  in
                     Prims.op_Negation uu____67572)
                   in
                if uu____67569
                then
                  let uu____67576 =
                    let uu____67582 =
                      let uu____67584 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____67586 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____67588 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____67584 uu____67586 uu____67588
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____67582)  in
                  FStar_Errors.raise_err uu____67576
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____67613 = mk_return env t1 s_e  in
                     ((M t1), uu____67613, u_e)))
               | (M t1,N t2) ->
                   let uu____67620 =
                     let uu____67626 =
                       let uu____67628 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____67630 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____67632 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____67628 uu____67630 uu____67632
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____67626)
                      in
                   FStar_Errors.raise_err uu____67620)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_67684 =
            match uu___590_67684 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____67700 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____67721 =
                let uu____67727 =
                  let uu____67729 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____67729
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____67727)  in
              FStar_Errors.raise_error uu____67721 e2.FStar_Syntax_Syntax.pos
          | M uu____67739 ->
              let uu____67740 = check env1 e2 context_nm  in
              strip_m uu____67740
           in
        let uu____67747 =
          let uu____67748 = FStar_Syntax_Subst.compress e  in
          uu____67748.FStar_Syntax_Syntax.n  in
        match uu____67747 with
        | FStar_Syntax_Syntax.Tm_bvar uu____67757 ->
            let uu____67758 = infer env e  in return_if uu____67758
        | FStar_Syntax_Syntax.Tm_name uu____67765 ->
            let uu____67766 = infer env e  in return_if uu____67766
        | FStar_Syntax_Syntax.Tm_fvar uu____67773 ->
            let uu____67774 = infer env e  in return_if uu____67774
        | FStar_Syntax_Syntax.Tm_abs uu____67781 ->
            let uu____67800 = infer env e  in return_if uu____67800
        | FStar_Syntax_Syntax.Tm_constant uu____67807 ->
            let uu____67808 = infer env e  in return_if uu____67808
        | FStar_Syntax_Syntax.Tm_quoted uu____67815 ->
            let uu____67822 = infer env e  in return_if uu____67822
        | FStar_Syntax_Syntax.Tm_app uu____67829 ->
            let uu____67846 = infer env e  in return_if uu____67846
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____67854 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____67854 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____67919) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____67925) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____67931,uu____67932) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____67973 ->
            let uu____67987 =
              let uu____67989 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____67989  in
            failwith uu____67987
        | FStar_Syntax_Syntax.Tm_type uu____67998 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____68006 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____68028 ->
            let uu____68035 =
              let uu____68037 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____68037  in
            failwith uu____68035
        | FStar_Syntax_Syntax.Tm_uvar uu____68046 ->
            let uu____68059 =
              let uu____68061 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____68061  in
            failwith uu____68059
        | FStar_Syntax_Syntax.Tm_delayed uu____68070 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____68100 =
              let uu____68102 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____68102  in
            failwith uu____68100

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
      let uu____68132 =
        let uu____68133 = FStar_Syntax_Subst.compress e  in
        uu____68133.FStar_Syntax_Syntax.n  in
      match uu____68132 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____68152 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____68152
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____68203;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____68204;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____68210 =
                  let uu___1360_68211 = rc  in
                  let uu____68212 =
                    let uu____68217 =
                      let uu____68220 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____68220  in
                    FStar_Pervasives_Native.Some uu____68217  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_68211.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____68212;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_68211.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____68210
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_68232 = env  in
            let uu____68233 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____68233;
              subst = (uu___1366_68232.subst);
              tc_const = (uu___1366_68232.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____68259  ->
                 match uu____68259 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_68282 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_68282.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_68282.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____68283 =
            FStar_List.fold_left
              (fun uu____68314  ->
                 fun uu____68315  ->
                   match (uu____68314, uu____68315) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____68373 = is_C c  in
                       if uu____68373
                       then
                         let xw =
                           let uu____68383 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____68383
                            in
                         let x =
                           let uu___1385_68386 = bv  in
                           let uu____68387 =
                             let uu____68390 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____68390  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_68386.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_68386.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____68387
                           }  in
                         let env3 =
                           let uu___1388_68392 = env2  in
                           let uu____68393 =
                             let uu____68396 =
                               let uu____68397 =
                                 let uu____68404 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____68404)  in
                               FStar_Syntax_Syntax.NT uu____68397  in
                             uu____68396 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_68392.tcenv);
                             subst = uu____68393;
                             tc_const = (uu___1388_68392.tc_const)
                           }  in
                         let uu____68409 =
                           let uu____68412 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____68413 =
                             let uu____68416 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____68416 :: acc  in
                           uu____68412 :: uu____68413  in
                         (env3, uu____68409)
                       else
                         (let x =
                            let uu___1391_68422 = bv  in
                            let uu____68423 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_68422.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_68422.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____68423
                            }  in
                          let uu____68426 =
                            let uu____68429 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____68429 :: acc  in
                          (env2, uu____68426))) (env1, []) binders1
             in
          (match uu____68283 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____68449 =
                 let check_what =
                   let uu____68475 = is_monadic rc_opt1  in
                   if uu____68475 then check_m else check_n  in
                 let uu____68492 = check_what env2 body1  in
                 match uu____68492 with
                 | (t,s_body,u_body) ->
                     let uu____68512 =
                       let uu____68515 =
                         let uu____68516 = is_monadic rc_opt1  in
                         if uu____68516 then M t else N t  in
                       comp_of_nm uu____68515  in
                     (uu____68512, s_body, u_body)
                  in
               (match uu____68449 with
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
                                 let uu____68556 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_68562  ->
                                           match uu___591_68562 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____68565 -> false))
                                    in
                                 if uu____68556
                                 then
                                   let uu____68568 =
                                     FStar_List.filter
                                       (fun uu___592_68572  ->
                                          match uu___592_68572 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____68575 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____68568
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____68586 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_68592  ->
                                         match uu___593_68592 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____68595 -> false))
                                  in
                               if uu____68586
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_68604  ->
                                        match uu___594_68604 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____68607 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____68609 =
                                   let uu____68610 =
                                     let uu____68615 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____68615
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____68610 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____68609
                               else
                                 (let uu____68622 =
                                    let uu___1432_68623 = rc  in
                                    let uu____68624 =
                                      let uu____68629 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____68629
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_68623.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____68624;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_68623.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____68622))
                       in
                    let uu____68634 =
                      let comp1 =
                        let uu____68642 = is_monadic rc_opt1  in
                        let uu____68644 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____68642 uu____68644
                         in
                      let uu____68645 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____68645,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____68634 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____68683 =
                             let uu____68684 =
                               let uu____68703 =
                                 let uu____68706 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____68706 s_rc_opt  in
                               (s_binders1, s_body1, uu____68703)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68684  in
                           mk1 uu____68683  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____68726 =
                             let uu____68727 =
                               let uu____68746 =
                                 let uu____68749 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____68749 u_rc_opt  in
                               (u_binders2, u_body2, uu____68746)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68727  in
                           mk1 uu____68726  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____68765;_};
            FStar_Syntax_Syntax.fv_delta = uu____68766;
            FStar_Syntax_Syntax.fv_qual = uu____68767;_}
          ->
          let uu____68770 =
            let uu____68775 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____68775  in
          (match uu____68770 with
           | (uu____68806,t) ->
               let uu____68808 =
                 let uu____68809 = normalize1 t  in N uu____68809  in
               (uu____68808, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____68810;
             FStar_Syntax_Syntax.vars = uu____68811;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____68890 = FStar_Syntax_Util.head_and_args e  in
          (match uu____68890 with
           | (unary_op1,uu____68914) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____68985;
             FStar_Syntax_Syntax.vars = uu____68986;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____69082 = FStar_Syntax_Util.head_and_args e  in
          (match uu____69082 with
           | (unary_op1,uu____69106) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69185;
             FStar_Syntax_Syntax.vars = uu____69186;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____69224 = infer env a  in
          (match uu____69224 with
           | (t,s,u) ->
               let uu____69240 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69240 with
                | (head1,uu____69264) ->
                    let uu____69289 =
                      let uu____69290 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____69290  in
                    let uu____69291 =
                      let uu____69292 =
                        let uu____69293 =
                          let uu____69310 =
                            let uu____69321 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69321]  in
                          (head1, uu____69310)  in
                        FStar_Syntax_Syntax.Tm_app uu____69293  in
                      mk1 uu____69292  in
                    let uu____69358 =
                      let uu____69359 =
                        let uu____69360 =
                          let uu____69377 =
                            let uu____69388 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69388]  in
                          (head1, uu____69377)  in
                        FStar_Syntax_Syntax.Tm_app uu____69360  in
                      mk1 uu____69359  in
                    (uu____69289, uu____69291, uu____69358)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69425;
             FStar_Syntax_Syntax.vars = uu____69426;_},(a1,uu____69428)::a2::[])
          ->
          let uu____69484 = infer env a1  in
          (match uu____69484 with
           | (t,s,u) ->
               let uu____69500 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69500 with
                | (head1,uu____69524) ->
                    let uu____69549 =
                      let uu____69550 =
                        let uu____69551 =
                          let uu____69568 =
                            let uu____69579 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69579; a2]  in
                          (head1, uu____69568)  in
                        FStar_Syntax_Syntax.Tm_app uu____69551  in
                      mk1 uu____69550  in
                    let uu____69624 =
                      let uu____69625 =
                        let uu____69626 =
                          let uu____69643 =
                            let uu____69654 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69654; a2]  in
                          (head1, uu____69643)  in
                        FStar_Syntax_Syntax.Tm_app uu____69626  in
                      mk1 uu____69625  in
                    (t, uu____69549, uu____69624)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69699;
             FStar_Syntax_Syntax.vars = uu____69700;_},uu____69701)
          ->
          let uu____69726 =
            let uu____69732 =
              let uu____69734 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69734
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69732)  in
          FStar_Errors.raise_error uu____69726 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69744;
             FStar_Syntax_Syntax.vars = uu____69745;_},uu____69746)
          ->
          let uu____69771 =
            let uu____69777 =
              let uu____69779 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69779
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69777)  in
          FStar_Errors.raise_error uu____69771 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____69815 = check_n env head1  in
          (match uu____69815 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____69838 =
                   let uu____69839 = FStar_Syntax_Subst.compress t  in
                   uu____69839.FStar_Syntax_Syntax.n  in
                 match uu____69838 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____69843 -> true
                 | uu____69859 -> false  in
               let rec flatten1 t =
                 let uu____69881 =
                   let uu____69882 = FStar_Syntax_Subst.compress t  in
                   uu____69882.FStar_Syntax_Syntax.n  in
                 match uu____69881 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____69901);
                                FStar_Syntax_Syntax.pos = uu____69902;
                                FStar_Syntax_Syntax.vars = uu____69903;_})
                     when is_arrow t1 ->
                     let uu____69932 = flatten1 t1  in
                     (match uu____69932 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____70032,uu____70033) -> flatten1 e1
                 | uu____70074 ->
                     let uu____70075 =
                       let uu____70081 =
                         let uu____70083 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____70083
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____70081)  in
                     FStar_Errors.raise_err uu____70075
                  in
               let uu____70101 = flatten1 t_head  in
               (match uu____70101 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____70176 =
                          let uu____70182 =
                            let uu____70184 = FStar_Util.string_of_int n1  in
                            let uu____70186 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____70188 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____70184 uu____70186 uu____70188
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____70182)
                           in
                        FStar_Errors.raise_err uu____70176)
                     else ();
                     (let uu____70194 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____70194 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____70247 args1 =
                            match uu____70247 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____70347 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____70347
                                 | (binders3,[]) ->
                                     let uu____70385 =
                                       let uu____70386 =
                                         let uu____70389 =
                                           let uu____70390 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____70390
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____70389
                                          in
                                       uu____70386.FStar_Syntax_Syntax.n  in
                                     (match uu____70385 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____70423 =
                                            let uu____70424 =
                                              let uu____70425 =
                                                let uu____70440 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____70440)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____70425
                                               in
                                            mk1 uu____70424  in
                                          N uu____70423
                                      | uu____70453 -> failwith "wat?")
                                 | ([],uu____70455::uu____70456) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____70509)::binders3,(arg,uu____70512)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____70599 = FStar_List.splitAt n' binders1
                             in
                          (match uu____70599 with
                           | (binders2,uu____70633) ->
                               let uu____70666 =
                                 let uu____70689 =
                                   FStar_List.map2
                                     (fun uu____70751  ->
                                        fun uu____70752  ->
                                          match (uu____70751, uu____70752)
                                          with
                                          | ((bv,uu____70800),(arg,q)) ->
                                              let uu____70829 =
                                                let uu____70830 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____70830.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____70829 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____70851 ->
                                                   let uu____70852 =
                                                     let uu____70859 =
                                                       star_type' env arg  in
                                                     (uu____70859, q)  in
                                                   (uu____70852, [(arg, q)])
                                               | uu____70896 ->
                                                   let uu____70897 =
                                                     check_n env arg  in
                                                   (match uu____70897 with
                                                    | (uu____70922,s_arg,u_arg)
                                                        ->
                                                        let uu____70925 =
                                                          let uu____70934 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____70934
                                                          then
                                                            let uu____70945 =
                                                              let uu____70952
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____70952,
                                                                q)
                                                               in
                                                            [uu____70945;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____70925))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____70689  in
                               (match uu____70666 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____71080 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____71093 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____71080, uu____71093)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____71162) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____71168) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____71174,uu____71175) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____71217 =
            let uu____71218 = env.tc_const c  in N uu____71218  in
          (uu____71217, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____71225 ->
          let uu____71239 =
            let uu____71241 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____71241  in
          failwith uu____71239
      | FStar_Syntax_Syntax.Tm_type uu____71250 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____71258 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____71280 ->
          let uu____71287 =
            let uu____71289 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____71289  in
          failwith uu____71287
      | FStar_Syntax_Syntax.Tm_uvar uu____71298 ->
          let uu____71311 =
            let uu____71313 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____71313  in
          failwith uu____71311
      | FStar_Syntax_Syntax.Tm_delayed uu____71322 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71352 =
            let uu____71354 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____71354  in
          failwith uu____71352

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
          let uu____71403 = check_n env e0  in
          match uu____71403 with
          | (uu____71416,s_e0,u_e0) ->
              let uu____71419 =
                let uu____71448 =
                  FStar_List.map
                    (fun b  ->
                       let uu____71509 = FStar_Syntax_Subst.open_branch b  in
                       match uu____71509 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_71551 = env  in
                             let uu____71552 =
                               let uu____71553 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____71553
                                in
                             {
                               tcenv = uu____71552;
                               subst = (uu___1707_71551.subst);
                               tc_const = (uu___1707_71551.tc_const)
                             }  in
                           let uu____71556 = f env1 body  in
                           (match uu____71556 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____71628 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____71448  in
              (match uu____71419 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____71734 = FStar_List.hd nms  in
                     match uu____71734 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_71743  ->
                          match uu___595_71743 with
                          | M uu____71745 -> true
                          | uu____71747 -> false) nms
                      in
                   let uu____71749 =
                     let uu____71786 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____71876  ->
                              match uu____71876 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____72060 =
                                         check env original_body (M t2)  in
                                       (match uu____72060 with
                                        | (uu____72097,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____72136,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____71786  in
                   (match uu____71749 with
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
                              (fun uu____72325  ->
                                 match uu____72325 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____72376 =
                                         let uu____72377 =
                                           let uu____72394 =
                                             let uu____72405 =
                                               let uu____72414 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____72417 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____72414, uu____72417)  in
                                             [uu____72405]  in
                                           (s_body, uu____72394)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____72377
                                          in
                                       mk1 uu____72376  in
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
                            let uu____72552 =
                              let uu____72553 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____72553]  in
                            let uu____72572 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____72552 uu____72572
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____72596 =
                              let uu____72605 =
                                let uu____72612 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____72612
                                 in
                              [uu____72605]  in
                            let uu____72631 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____72596 uu____72631
                             in
                          let uu____72634 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____72673 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____72634, uu____72673)
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
                           let uu____72783 =
                             let uu____72784 =
                               let uu____72785 =
                                 let uu____72812 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____72812,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____72785
                                in
                             mk1 uu____72784  in
                           let uu____72871 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____72783, uu____72871))))

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
              let uu____72936 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____72936]  in
            let uu____72955 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____72955 with
            | (x_binders1,e21) ->
                let uu____72968 = infer env e1  in
                (match uu____72968 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____72985 = is_C t1  in
                       if uu____72985
                       then
                         let uu___1793_72988 = binding  in
                         let uu____72989 =
                           let uu____72992 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____72992  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_72988.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_72988.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____72989;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_72988.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_72988.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_72988.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_72988.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_72996 = env  in
                       let uu____72997 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_72999 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_72999.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_72999.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____72997;
                         subst = (uu___1796_72996.subst);
                         tc_const = (uu___1796_72996.tc_const)
                       }  in
                     let uu____73000 = proceed env1 e21  in
                     (match uu____73000 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_73017 = binding  in
                            let uu____73018 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_73017.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_73017.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____73018;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_73017.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_73017.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_73017.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_73017.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____73021 =
                            let uu____73022 =
                              let uu____73023 =
                                let uu____73037 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_73054 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_73054.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_73054.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_73054.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_73054.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_73054.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_73054.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73037)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73023  in
                            mk1 uu____73022  in
                          let uu____73055 =
                            let uu____73056 =
                              let uu____73057 =
                                let uu____73071 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_73088 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_73088.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_73088.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_73088.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_73088.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_73088.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_73088.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73071)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73057  in
                            mk1 uu____73056  in
                          (nm_rec, uu____73021, uu____73055))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_73093 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_73093.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_73093.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_73093.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_73093.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_73093.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_73095 = env  in
                       let uu____73096 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_73098 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_73098.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_73098.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73096;
                         subst = (uu___1820_73095.subst);
                         tc_const = (uu___1820_73095.tc_const)
                       }  in
                     let uu____73099 = ensure_m env1 e21  in
                     (match uu____73099 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____73123 =
                              let uu____73124 =
                                let uu____73141 =
                                  let uu____73152 =
                                    let uu____73161 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____73164 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____73161, uu____73164)  in
                                  [uu____73152]  in
                                (s_e2, uu____73141)  in
                              FStar_Syntax_Syntax.Tm_app uu____73124  in
                            mk1 uu____73123  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____73206 =
                              let uu____73207 =
                                let uu____73224 =
                                  let uu____73235 =
                                    let uu____73244 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____73244)  in
                                  [uu____73235]  in
                                (s_e1, uu____73224)  in
                              FStar_Syntax_Syntax.Tm_app uu____73207  in
                            mk1 uu____73206  in
                          let uu____73280 =
                            let uu____73281 =
                              let uu____73282 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____73282]  in
                            FStar_Syntax_Util.abs uu____73281 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____73301 =
                            let uu____73302 =
                              let uu____73303 =
                                let uu____73317 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_73334 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_73334.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_73334.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_73334.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_73334.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_73334.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_73334.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73317)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73303  in
                            mk1 uu____73302  in
                          ((M t2), uu____73280, uu____73301)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73344 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____73344  in
      let uu____73345 = check env e mn  in
      match uu____73345 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73361 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73384 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____73384  in
      let uu____73385 = check env e mn  in
      match uu____73385 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73401 -> failwith "[check_m]: impossible"

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
        (let uu____73434 =
           let uu____73436 = is_C c  in Prims.op_Negation uu____73436  in
         if uu____73434 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____73450 =
           let uu____73451 = FStar_Syntax_Subst.compress c  in
           uu____73451.FStar_Syntax_Syntax.n  in
         match uu____73450 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____73480 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____73480 with
              | (wp_head,wp_args) ->
                  ((let uu____73524 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____73543 =
                           let uu____73545 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____73545
                            in
                         Prims.op_Negation uu____73543)
                       in
                    if uu____73524 then failwith "mismatch" else ());
                   (let uu____73558 =
                      let uu____73559 =
                        let uu____73576 =
                          FStar_List.map2
                            (fun uu____73614  ->
                               fun uu____73615  ->
                                 match (uu____73614, uu____73615) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____73677 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____73677
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____73686 =
                                         let uu____73688 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____73688 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____73686
                                       then
                                         let uu____73690 =
                                           let uu____73696 =
                                             let uu____73698 =
                                               print_implicit q  in
                                             let uu____73700 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____73698 uu____73700
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____73696)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____73690
                                       else ());
                                      (let uu____73706 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____73706, q)))) args wp_args
                           in
                        (head1, uu____73576)  in
                      FStar_Syntax_Syntax.Tm_app uu____73559  in
                    mk1 uu____73558)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____73752 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____73752 with
              | (binders_orig,comp1) ->
                  let uu____73759 =
                    let uu____73776 =
                      FStar_List.map
                        (fun uu____73816  ->
                           match uu____73816 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____73844 = is_C h  in
                               if uu____73844
                               then
                                 let w' =
                                   let uu____73860 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____73860
                                    in
                                 let uu____73862 =
                                   let uu____73871 =
                                     let uu____73880 =
                                       let uu____73887 =
                                         let uu____73888 =
                                           let uu____73889 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____73889  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____73888
                                          in
                                       (uu____73887, q)  in
                                     [uu____73880]  in
                                   (w', q) :: uu____73871  in
                                 (w', uu____73862)
                               else
                                 (let x =
                                    let uu____73923 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____73923
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____73776  in
                  (match uu____73759 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____73997 =
                           let uu____74000 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____74000
                            in
                         FStar_Syntax_Subst.subst_comp uu____73997 comp1  in
                       let app =
                         let uu____74004 =
                           let uu____74005 =
                             let uu____74022 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____74041 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____74042 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____74041, uu____74042)) bvs
                                in
                             (wp, uu____74022)  in
                           FStar_Syntax_Syntax.Tm_app uu____74005  in
                         mk1 uu____74004  in
                       let comp3 =
                         let uu____74057 = type_of_comp comp2  in
                         let uu____74058 = is_monadic_comp comp2  in
                         trans_G env uu____74057 uu____74058 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____74061,uu____74062) ->
             trans_F_ env e wp
         | uu____74103 -> failwith "impossible trans_F_")

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
            let uu____74111 =
              let uu____74112 = star_type' env h  in
              let uu____74115 =
                let uu____74126 =
                  let uu____74135 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____74135)  in
                [uu____74126]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____74112;
                FStar_Syntax_Syntax.effect_args = uu____74115;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____74111
          else
            (let uu____74161 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____74161)

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
    fun t  -> let uu____74182 = n env.tcenv t  in star_type' env uu____74182
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____74202 = n env.tcenv t  in check_n env uu____74202
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____74219 = n env.tcenv c  in
        let uu____74220 = n env.tcenv wp  in
        trans_F_ env uu____74219 uu____74220
  