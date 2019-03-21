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
              let uu___613_61042 = a  in
              let uu____61043 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_61042.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_61042.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____61043
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____61056 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____61056
             then
               (d "Elaborating extra WP combinators";
                (let uu____61062 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____61062))
             else ());
            (let rec collect_binders t =
               let uu____61081 =
                 let uu____61082 =
                   let uu____61085 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____61085
                    in
                 uu____61082.FStar_Syntax_Syntax.n  in
               match uu____61081 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____61120) -> t1
                     | uu____61129 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____61131 = collect_binders rest  in
                   FStar_List.append bs uu____61131
               | FStar_Syntax_Syntax.Tm_type uu____61146 -> []
               | uu____61153 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____61180 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____61180
                 FStar_Syntax_Util.name_binders
                in
             (let uu____61206 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____61206
              then
                let uu____61210 =
                  let uu____61212 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____61212  in
                d uu____61210
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____61250 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____61250 with
                | (sigelt,fv) ->
                    ((let uu____61258 =
                        let uu____61261 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____61261
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____61258);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____61341  ->
                     match uu____61341 with
                     | (t,b) ->
                         let uu____61355 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____61355))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____61394 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____61394))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____61428 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____61428)
                 in
              let uu____61431 =
                let uu____61448 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____61473 =
                        let uu____61476 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____61476  in
                      FStar_Syntax_Util.arrow gamma uu____61473  in
                    let uu____61477 =
                      let uu____61478 =
                        let uu____61487 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____61494 =
                          let uu____61503 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____61503]  in
                        uu____61487 :: uu____61494  in
                      FStar_List.append binders uu____61478  in
                    FStar_Syntax_Util.abs uu____61477 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____61534 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____61535 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____61534, uu____61535)  in
                match uu____61448 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____61577 =
                        let uu____61578 =
                          let uu____61595 =
                            let uu____61606 =
                              FStar_List.map
                                (fun uu____61628  ->
                                   match uu____61628 with
                                   | (bv,uu____61640) ->
                                       let uu____61645 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____61646 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____61645, uu____61646)) binders
                               in
                            let uu____61648 =
                              let uu____61655 =
                                let uu____61660 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____61661 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____61660, uu____61661)  in
                              let uu____61663 =
                                let uu____61670 =
                                  let uu____61675 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____61675)  in
                                [uu____61670]  in
                              uu____61655 :: uu____61663  in
                            FStar_List.append uu____61606 uu____61648  in
                          (fv, uu____61595)  in
                        FStar_Syntax_Syntax.Tm_app uu____61578  in
                      mk1 uu____61577  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____61431 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____61748 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____61748
                       in
                    let ret1 =
                      let uu____61753 =
                        let uu____61754 =
                          let uu____61757 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____61757  in
                        FStar_Syntax_Util.residual_tot uu____61754  in
                      FStar_Pervasives_Native.Some uu____61753  in
                    let body =
                      let uu____61761 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____61761 ret1  in
                    let uu____61764 =
                      let uu____61765 = mk_all_implicit binders  in
                      let uu____61772 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____61765 uu____61772  in
                    FStar_Syntax_Util.abs uu____61764 body ret1  in
                  let c_pure1 =
                    let uu____61810 = mk_lid "pure"  in
                    register env1 uu____61810 c_pure  in
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
                      let uu____61820 =
                        let uu____61821 =
                          let uu____61822 =
                            let uu____61831 =
                              let uu____61838 =
                                let uu____61839 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____61839
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____61838  in
                            [uu____61831]  in
                          let uu____61852 =
                            let uu____61855 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____61855  in
                          FStar_Syntax_Util.arrow uu____61822 uu____61852  in
                        mk_gctx uu____61821  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____61820
                       in
                    let r =
                      let uu____61858 =
                        let uu____61859 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____61859  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____61858
                       in
                    let ret1 =
                      let uu____61864 =
                        let uu____61865 =
                          let uu____61868 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____61868  in
                        FStar_Syntax_Util.residual_tot uu____61865  in
                      FStar_Pervasives_Native.Some uu____61864  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____61878 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____61881 =
                          let uu____61892 =
                            let uu____61895 =
                              let uu____61896 =
                                let uu____61897 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____61897
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____61896  in
                            [uu____61895]  in
                          FStar_List.append gamma_as_args uu____61892  in
                        FStar_Syntax_Util.mk_app uu____61878 uu____61881  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____61900 =
                      let uu____61901 = mk_all_implicit binders  in
                      let uu____61908 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____61901 uu____61908  in
                    FStar_Syntax_Util.abs uu____61900 outer_body ret1  in
                  let c_app1 =
                    let uu____61960 = mk_lid "app"  in
                    register env1 uu____61960 c_app  in
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
                      let uu____61972 =
                        let uu____61981 =
                          let uu____61988 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____61988  in
                        [uu____61981]  in
                      let uu____62001 =
                        let uu____62004 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62004  in
                      FStar_Syntax_Util.arrow uu____61972 uu____62001  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62008 =
                        let uu____62009 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62009  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62008
                       in
                    let ret1 =
                      let uu____62014 =
                        let uu____62015 =
                          let uu____62018 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62018  in
                        FStar_Syntax_Util.residual_tot uu____62015  in
                      FStar_Pervasives_Native.Some uu____62014  in
                    let uu____62019 =
                      let uu____62020 = mk_all_implicit binders  in
                      let uu____62027 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____62020 uu____62027  in
                    let uu____62078 =
                      let uu____62081 =
                        let uu____62092 =
                          let uu____62095 =
                            let uu____62096 =
                              let uu____62107 =
                                let uu____62110 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____62110]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62107
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62096  in
                          let uu____62119 =
                            let uu____62122 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____62122]  in
                          uu____62095 :: uu____62119  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62092
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62081  in
                    FStar_Syntax_Util.abs uu____62019 uu____62078 ret1  in
                  let c_lift11 =
                    let uu____62132 = mk_lid "lift1"  in
                    register env1 uu____62132 c_lift1  in
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
                      let uu____62146 =
                        let uu____62155 =
                          let uu____62162 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62162  in
                        let uu____62163 =
                          let uu____62172 =
                            let uu____62179 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____62179  in
                          [uu____62172]  in
                        uu____62155 :: uu____62163  in
                      let uu____62198 =
                        let uu____62201 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62201  in
                      FStar_Syntax_Util.arrow uu____62146 uu____62198  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62205 =
                        let uu____62206 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62206  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62205
                       in
                    let a2 =
                      let uu____62209 =
                        let uu____62210 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____62210  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____62209
                       in
                    let ret1 =
                      let uu____62215 =
                        let uu____62216 =
                          let uu____62219 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____62219  in
                        FStar_Syntax_Util.residual_tot uu____62216  in
                      FStar_Pervasives_Native.Some uu____62215  in
                    let uu____62220 =
                      let uu____62221 = mk_all_implicit binders  in
                      let uu____62228 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____62221 uu____62228  in
                    let uu____62293 =
                      let uu____62296 =
                        let uu____62307 =
                          let uu____62310 =
                            let uu____62311 =
                              let uu____62322 =
                                let uu____62325 =
                                  let uu____62326 =
                                    let uu____62337 =
                                      let uu____62340 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____62340]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____62337
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____62326
                                   in
                                let uu____62349 =
                                  let uu____62352 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____62352]  in
                                uu____62325 :: uu____62349  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62322
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____62311  in
                          let uu____62361 =
                            let uu____62364 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____62364]  in
                          uu____62310 :: uu____62361  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62307
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62296  in
                    FStar_Syntax_Util.abs uu____62220 uu____62293 ret1  in
                  let c_lift21 =
                    let uu____62374 = mk_lid "lift2"  in
                    register env1 uu____62374 c_lift2  in
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
                      let uu____62386 =
                        let uu____62395 =
                          let uu____62402 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62402  in
                        [uu____62395]  in
                      let uu____62415 =
                        let uu____62418 =
                          let uu____62419 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62419  in
                        FStar_Syntax_Syntax.mk_Total uu____62418  in
                      FStar_Syntax_Util.arrow uu____62386 uu____62415  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____62425 =
                        let uu____62426 =
                          let uu____62429 =
                            let uu____62430 =
                              let uu____62439 =
                                let uu____62446 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____62446
                                 in
                              [uu____62439]  in
                            let uu____62459 =
                              let uu____62462 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____62462  in
                            FStar_Syntax_Util.arrow uu____62430 uu____62459
                             in
                          mk_ctx uu____62429  in
                        FStar_Syntax_Util.residual_tot uu____62426  in
                      FStar_Pervasives_Native.Some uu____62425  in
                    let e1 =
                      let uu____62464 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____62464
                       in
                    let body =
                      let uu____62469 =
                        let uu____62470 =
                          let uu____62479 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____62479]  in
                        FStar_List.append gamma uu____62470  in
                      let uu____62504 =
                        let uu____62507 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____62510 =
                          let uu____62521 =
                            let uu____62522 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____62522  in
                          let uu____62523 = args_of_binders1 gamma  in
                          uu____62521 :: uu____62523  in
                        FStar_Syntax_Util.mk_app uu____62507 uu____62510  in
                      FStar_Syntax_Util.abs uu____62469 uu____62504 ret1  in
                    let uu____62526 =
                      let uu____62527 = mk_all_implicit binders  in
                      let uu____62534 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____62527 uu____62534  in
                    FStar_Syntax_Util.abs uu____62526 body ret1  in
                  let c_push1 =
                    let uu____62579 = mk_lid "push"  in
                    register env1 uu____62579 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____62606 =
                        let uu____62607 =
                          let uu____62624 = args_of_binders1 binders  in
                          (c, uu____62624)  in
                        FStar_Syntax_Syntax.Tm_app uu____62607  in
                      mk1 uu____62606
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____62653 =
                        let uu____62654 =
                          let uu____62663 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____62670 =
                            let uu____62679 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____62679]  in
                          uu____62663 :: uu____62670  in
                        let uu____62704 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____62654 uu____62704  in
                      FStar_Syntax_Syntax.mk_Total uu____62653  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____62709 =
                      let uu____62710 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____62710  in
                    let uu____62725 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____62730 =
                        let uu____62733 =
                          let uu____62744 =
                            let uu____62747 =
                              let uu____62748 =
                                let uu____62759 =
                                  let uu____62768 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____62768  in
                                [uu____62759]  in
                              FStar_Syntax_Util.mk_app l_ite uu____62748  in
                            [uu____62747]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____62744
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____62733  in
                      FStar_Syntax_Util.ascribe uu____62730
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____62709 uu____62725
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____62812 = mk_lid "wp_if_then_else"  in
                    register env1 uu____62812 wp_if_then_else  in
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
                      let uu____62829 =
                        let uu____62840 =
                          let uu____62843 =
                            let uu____62844 =
                              let uu____62855 =
                                let uu____62858 =
                                  let uu____62859 =
                                    let uu____62870 =
                                      let uu____62879 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62879
                                       in
                                    [uu____62870]  in
                                  FStar_Syntax_Util.mk_app l_and uu____62859
                                   in
                                [uu____62858]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62855
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62844  in
                          let uu____62904 =
                            let uu____62907 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____62907]  in
                          uu____62843 :: uu____62904  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62840
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62829  in
                    let uu____62916 =
                      let uu____62917 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____62917  in
                    FStar_Syntax_Util.abs uu____62916 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____62933 = mk_lid "wp_assert"  in
                    register env1 uu____62933 wp_assert  in
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
                      let uu____62950 =
                        let uu____62961 =
                          let uu____62964 =
                            let uu____62965 =
                              let uu____62976 =
                                let uu____62979 =
                                  let uu____62980 =
                                    let uu____62991 =
                                      let uu____63000 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____63000
                                       in
                                    [uu____62991]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____62980
                                   in
                                [uu____62979]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62976
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62965  in
                          let uu____63025 =
                            let uu____63028 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____63028]  in
                          uu____62964 :: uu____63025  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62961
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62950  in
                    let uu____63037 =
                      let uu____63038 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____63038  in
                    FStar_Syntax_Util.abs uu____63037 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____63054 = mk_lid "wp_assume"  in
                    register env1 uu____63054 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____63067 =
                        let uu____63076 =
                          let uu____63083 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____63083  in
                        [uu____63076]  in
                      let uu____63096 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____63067 uu____63096  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____63104 =
                        let uu____63115 =
                          let uu____63118 =
                            let uu____63119 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____63119  in
                          let uu____63138 =
                            let uu____63141 =
                              let uu____63142 =
                                let uu____63153 =
                                  let uu____63156 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____63156]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____63153
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____63142
                               in
                            [uu____63141]  in
                          uu____63118 :: uu____63138  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63115
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63104  in
                    let uu____63173 =
                      let uu____63174 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____63174  in
                    FStar_Syntax_Util.abs uu____63173 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____63190 = mk_lid "wp_close"  in
                    register env1 uu____63190 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____63201 =
                      let uu____63202 =
                        let uu____63203 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____63203
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____63202
                       in
                    FStar_Pervasives_Native.Some uu____63201  in
                  let mk_forall1 x body =
                    let uu____63215 =
                      let uu____63222 =
                        let uu____63223 =
                          let uu____63240 =
                            let uu____63251 =
                              let uu____63260 =
                                let uu____63261 =
                                  let uu____63262 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____63262]  in
                                FStar_Syntax_Util.abs uu____63261 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____63260  in
                            [uu____63251]  in
                          (FStar_Syntax_Util.tforall, uu____63240)  in
                        FStar_Syntax_Syntax.Tm_app uu____63223  in
                      FStar_Syntax_Syntax.mk uu____63222  in
                    uu____63215 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____63320 =
                      let uu____63321 = FStar_Syntax_Subst.compress t  in
                      uu____63321.FStar_Syntax_Syntax.n  in
                    match uu____63320 with
                    | FStar_Syntax_Syntax.Tm_type uu____63325 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63358  ->
                              match uu____63358 with
                              | (b,uu____63367) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____63372 -> true  in
                  let rec is_monotonic t =
                    let uu____63385 =
                      let uu____63386 = FStar_Syntax_Subst.compress t  in
                      uu____63386.FStar_Syntax_Syntax.n  in
                    match uu____63385 with
                    | FStar_Syntax_Syntax.Tm_type uu____63390 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63423  ->
                              match uu____63423 with
                              | (b,uu____63432) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____63437 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____63511 =
                      let uu____63512 = FStar_Syntax_Subst.compress t1  in
                      uu____63512.FStar_Syntax_Syntax.n  in
                    match uu____63511 with
                    | FStar_Syntax_Syntax.Tm_type uu____63517 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____63520);
                                      FStar_Syntax_Syntax.pos = uu____63521;
                                      FStar_Syntax_Syntax.vars = uu____63522;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63566 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63566
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63576 =
                              let uu____63579 =
                                let uu____63590 =
                                  let uu____63599 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63599  in
                                [uu____63590]  in
                              FStar_Syntax_Util.mk_app x uu____63579  in
                            let uu____63616 =
                              let uu____63619 =
                                let uu____63630 =
                                  let uu____63639 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63639  in
                                [uu____63630]  in
                              FStar_Syntax_Util.mk_app y uu____63619  in
                            mk_rel1 b uu____63576 uu____63616  in
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
                             let uu____63663 =
                               let uu____63666 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63669 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63666 uu____63669  in
                             let uu____63672 =
                               let uu____63675 =
                                 let uu____63678 =
                                   let uu____63689 =
                                     let uu____63698 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63698
                                      in
                                   [uu____63689]  in
                                 FStar_Syntax_Util.mk_app x uu____63678  in
                               let uu____63715 =
                                 let uu____63718 =
                                   let uu____63729 =
                                     let uu____63738 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63738
                                      in
                                   [uu____63729]  in
                                 FStar_Syntax_Util.mk_app y uu____63718  in
                               mk_rel1 b uu____63675 uu____63715  in
                             FStar_Syntax_Util.mk_imp uu____63663 uu____63672
                              in
                           let uu____63755 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63755)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____63758);
                                      FStar_Syntax_Syntax.pos = uu____63759;
                                      FStar_Syntax_Syntax.vars = uu____63760;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63804 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63804
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63814 =
                              let uu____63817 =
                                let uu____63828 =
                                  let uu____63837 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63837  in
                                [uu____63828]  in
                              FStar_Syntax_Util.mk_app x uu____63817  in
                            let uu____63854 =
                              let uu____63857 =
                                let uu____63868 =
                                  let uu____63877 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63877  in
                                [uu____63868]  in
                              FStar_Syntax_Util.mk_app y uu____63857  in
                            mk_rel1 b uu____63814 uu____63854  in
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
                             let uu____63901 =
                               let uu____63904 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63907 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63904 uu____63907  in
                             let uu____63910 =
                               let uu____63913 =
                                 let uu____63916 =
                                   let uu____63927 =
                                     let uu____63936 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63936
                                      in
                                   [uu____63927]  in
                                 FStar_Syntax_Util.mk_app x uu____63916  in
                               let uu____63953 =
                                 let uu____63956 =
                                   let uu____63967 =
                                     let uu____63976 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63976
                                      in
                                   [uu____63967]  in
                                 FStar_Syntax_Util.mk_app y uu____63956  in
                               mk_rel1 b uu____63913 uu____63953  in
                             FStar_Syntax_Util.mk_imp uu____63901 uu____63910
                              in
                           let uu____63993 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63993)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_64032 = t1  in
                          let uu____64033 =
                            let uu____64034 =
                              let uu____64049 =
                                let uu____64052 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____64052  in
                              ([binder], uu____64049)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____64034  in
                          {
                            FStar_Syntax_Syntax.n = uu____64033;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_64032.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_64032.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____64075 ->
                        failwith "unhandled arrow"
                    | uu____64093 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____64130 =
                        let uu____64131 = FStar_Syntax_Subst.compress t1  in
                        uu____64131.FStar_Syntax_Syntax.n  in
                      match uu____64130 with
                      | FStar_Syntax_Syntax.Tm_type uu____64134 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____64161 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____64161
                          ->
                          let project i tuple =
                            let projector =
                              let uu____64182 =
                                let uu____64183 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____64183 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____64182
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____64213 =
                            let uu____64224 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____64242  ->
                                     match uu____64242 with
                                     | (t2,q) ->
                                         let uu____64262 = project i x  in
                                         let uu____64265 = project i y  in
                                         mk_stronger t2 uu____64262
                                           uu____64265) args
                               in
                            match uu____64224 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____64213 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____64319);
                                      FStar_Syntax_Syntax.pos = uu____64320;
                                      FStar_Syntax_Syntax.vars = uu____64321;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64365  ->
                                   match uu____64365 with
                                   | (bv,q) ->
                                       let uu____64379 =
                                         let uu____64381 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64381  in
                                       FStar_Syntax_Syntax.gen_bv uu____64379
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64390 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64390) bvs
                             in
                          let body =
                            let uu____64392 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64395 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64392 uu____64395  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____64404);
                                      FStar_Syntax_Syntax.pos = uu____64405;
                                      FStar_Syntax_Syntax.vars = uu____64406;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64450  ->
                                   match uu____64450 with
                                   | (bv,q) ->
                                       let uu____64464 =
                                         let uu____64466 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64466  in
                                       FStar_Syntax_Syntax.gen_bv uu____64464
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64475 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64475) bvs
                             in
                          let body =
                            let uu____64477 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64480 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64477 uu____64480  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____64487 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____64490 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____64493 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____64496 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____64490 uu____64493 uu____64496  in
                    let uu____64499 =
                      let uu____64500 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____64500  in
                    FStar_Syntax_Util.abs uu____64499 body ret_tot_type  in
                  let stronger1 =
                    let uu____64542 = mk_lid "stronger"  in
                    register env1 uu____64542 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64550 = FStar_Util.prefix gamma  in
                    match uu____64550 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____64616 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____64616
                             in
                          let uu____64621 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____64621 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____64631 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____64631  in
                              let guard_free1 =
                                let uu____64643 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____64643  in
                              let pat =
                                let uu____64647 =
                                  let uu____64658 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____64658]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____64647
                                 in
                              let pattern_guarded_body =
                                let uu____64686 =
                                  let uu____64687 =
                                    let uu____64694 =
                                      let uu____64695 =
                                        let uu____64708 =
                                          let uu____64719 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____64719]  in
                                        [uu____64708]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____64695
                                       in
                                    (body, uu____64694)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____64687  in
                                mk1 uu____64686  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____64766 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____64775 =
                            let uu____64778 =
                              let uu____64779 =
                                let uu____64782 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____64785 =
                                  let uu____64796 = args_of_binders1 wp_args
                                     in
                                  let uu____64799 =
                                    let uu____64802 =
                                      let uu____64803 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____64803
                                       in
                                    [uu____64802]  in
                                  FStar_List.append uu____64796 uu____64799
                                   in
                                FStar_Syntax_Util.mk_app uu____64782
                                  uu____64785
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____64779  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____64778
                             in
                          FStar_Syntax_Util.abs gamma uu____64775
                            ret_gtot_type
                           in
                        let uu____64804 =
                          let uu____64805 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____64805  in
                        FStar_Syntax_Util.abs uu____64804 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____64821 = mk_lid "ite_wp"  in
                    register env1 uu____64821 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64829 = FStar_Util.prefix gamma  in
                    match uu____64829 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____64887 =
                            let uu____64888 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____64895 =
                              let uu____64906 =
                                let uu____64915 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____64915  in
                              [uu____64906]  in
                            FStar_Syntax_Util.mk_app uu____64888 uu____64895
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____64887
                           in
                        let uu____64932 =
                          let uu____64933 =
                            let uu____64942 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____64942 gamma  in
                          FStar_List.append binders uu____64933  in
                        FStar_Syntax_Util.abs uu____64932 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____64964 = mk_lid "null_wp"  in
                    register env1 uu____64964 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____64977 =
                        let uu____64988 =
                          let uu____64991 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____64992 =
                            let uu____64995 =
                              let uu____64996 =
                                let uu____65007 =
                                  let uu____65016 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____65016  in
                                [uu____65007]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____64996
                               in
                            let uu____65033 =
                              let uu____65036 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____65036]  in
                            uu____64995 :: uu____65033  in
                          uu____64991 :: uu____64992  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____64988
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____64977  in
                    let uu____65045 =
                      let uu____65046 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____65046  in
                    FStar_Syntax_Util.abs uu____65045 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____65062 = mk_lid "wp_trivial"  in
                    register env1 uu____65062 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____65068 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____65068
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____65080 =
                      let uu____65081 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____65081  in
                    let uu____65107 =
                      let uu___934_65108 = ed  in
                      let uu____65109 =
                        let uu____65110 = c wp_if_then_else2  in
                        ([], uu____65110)  in
                      let uu____65117 =
                        let uu____65118 = c ite_wp2  in ([], uu____65118)  in
                      let uu____65125 =
                        let uu____65126 = c stronger2  in ([], uu____65126)
                         in
                      let uu____65133 =
                        let uu____65134 = c wp_close2  in ([], uu____65134)
                         in
                      let uu____65141 =
                        let uu____65142 = c wp_assert2  in ([], uu____65142)
                         in
                      let uu____65149 =
                        let uu____65150 = c wp_assume2  in ([], uu____65150)
                         in
                      let uu____65157 =
                        let uu____65158 = c null_wp2  in ([], uu____65158)
                         in
                      let uu____65165 =
                        let uu____65166 = c wp_trivial2  in ([], uu____65166)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_65108.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_65108.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_65108.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_65108.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_65108.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_65108.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_65108.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____65109;
                        FStar_Syntax_Syntax.ite_wp = uu____65117;
                        FStar_Syntax_Syntax.stronger = uu____65125;
                        FStar_Syntax_Syntax.close_wp = uu____65133;
                        FStar_Syntax_Syntax.assert_p = uu____65141;
                        FStar_Syntax_Syntax.assume_p = uu____65149;
                        FStar_Syntax_Syntax.null_wp = uu____65157;
                        FStar_Syntax_Syntax.trivial = uu____65165;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_65108.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_65108.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_65108.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_65108.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_65108.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____65080, uu____65107)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_65190 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_65190.subst);
        tc_const = (uu___939_65190.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____65211 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____65230 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65250) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_65264  ->
                match uu___585_65264 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____65267 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____65269 ->
        let uu____65270 =
          let uu____65276 =
            let uu____65278 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____65278
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____65276)  in
        FStar_Errors.raise_error uu____65270 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_65288  ->
    match uu___586_65288 with
    | N t ->
        let uu____65291 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____65291
    | M t ->
        let uu____65295 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____65295
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____65304,c) -> nm_of_comp c
    | uu____65326 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____65339 = nm_of_comp c  in
    match uu____65339 with | M uu____65341 -> true | N uu____65343 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____65354 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____65370 =
        let uu____65379 =
          let uu____65386 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____65386  in
        [uu____65379]  in
      let uu____65405 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____65370 uu____65405  in
    let uu____65408 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____65408
  
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
        let uu____65450 =
          let uu____65451 =
            let uu____65466 =
              let uu____65475 =
                let uu____65482 =
                  let uu____65483 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____65483  in
                let uu____65484 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____65482, uu____65484)  in
              [uu____65475]  in
            let uu____65502 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____65466, uu____65502)  in
          FStar_Syntax_Syntax.Tm_arrow uu____65451  in
        mk1 uu____65450

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____65542) ->
          let binders1 =
            FStar_List.map
              (fun uu____65588  ->
                 match uu____65588 with
                 | (bv,aqual) ->
                     let uu____65607 =
                       let uu___989_65608 = bv  in
                       let uu____65609 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_65608.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_65608.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____65609
                       }  in
                     (uu____65607, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____65614,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____65616);
                              FStar_Syntax_Syntax.pos = uu____65617;
                              FStar_Syntax_Syntax.vars = uu____65618;_})
               ->
               let uu____65647 =
                 let uu____65648 =
                   let uu____65663 =
                     let uu____65666 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____65666  in
                   (binders1, uu____65663)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____65648  in
               mk1 uu____65647
           | uu____65677 ->
               let uu____65678 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____65678 with
                | N hn ->
                    let uu____65680 =
                      let uu____65681 =
                        let uu____65696 =
                          let uu____65699 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____65699  in
                        (binders1, uu____65696)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65681  in
                    mk1 uu____65680
                | M a ->
                    let uu____65711 =
                      let uu____65712 =
                        let uu____65727 =
                          let uu____65736 =
                            let uu____65745 =
                              let uu____65752 =
                                let uu____65753 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____65753  in
                              let uu____65754 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____65752, uu____65754)  in
                            [uu____65745]  in
                          FStar_List.append binders1 uu____65736  in
                        let uu____65778 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____65727, uu____65778)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65712  in
                    mk1 uu____65711))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____65872 = f x  in
                    FStar_Util.string_builder_append strb uu____65872);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____65881 = f x1  in
                         FStar_Util.string_builder_append strb uu____65881))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____65885 =
              let uu____65891 =
                let uu____65893 = FStar_Syntax_Print.term_to_string t2  in
                let uu____65895 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____65893 uu____65895
                 in
              (FStar_Errors.Warning_DependencyFound, uu____65891)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____65885  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____65917 =
              let uu____65918 = FStar_Syntax_Subst.compress ty  in
              uu____65918.FStar_Syntax_Syntax.n  in
            match uu____65917 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____65944 =
                  let uu____65946 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____65946  in
                if uu____65944
                then false
                else
                  (try
                     (fun uu___1038_65963  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____65987 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____65987 s  in
                              let uu____65990 =
                                let uu____65992 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____65992  in
                              if uu____65990
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____65998 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____65998 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____66023  ->
                                          match uu____66023 with
                                          | (bv,uu____66035) ->
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
            | uu____66063 ->
                ((let uu____66065 =
                    let uu____66071 =
                      let uu____66073 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____66073
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____66071)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____66065);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____66089 =
              let uu____66090 = FStar_Syntax_Subst.compress head2  in
              uu____66090.FStar_Syntax_Syntax.n  in
            match uu____66089 with
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
                  (let uu____66096 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____66096)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____66099 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____66099 with
                 | ((uu____66109,ty),uu____66111) ->
                     let uu____66116 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____66116
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____66129 =
                         let uu____66130 = FStar_Syntax_Subst.compress res
                            in
                         uu____66130.FStar_Syntax_Syntax.n  in
                       (match uu____66129 with
                        | FStar_Syntax_Syntax.Tm_app uu____66134 -> true
                        | uu____66152 ->
                            ((let uu____66154 =
                                let uu____66160 =
                                  let uu____66162 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____66162
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____66160)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____66154);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____66170 -> true
            | FStar_Syntax_Syntax.Tm_name uu____66172 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____66175) ->
                is_valid_application t2
            | uu____66180 -> false  in
          let uu____66182 = is_valid_application head1  in
          if uu____66182
          then
            let uu____66185 =
              let uu____66186 =
                let uu____66203 =
                  FStar_List.map
                    (fun uu____66232  ->
                       match uu____66232 with
                       | (t2,qual) ->
                           let uu____66257 = star_type' env t2  in
                           (uu____66257, qual)) args
                   in
                (head1, uu____66203)  in
              FStar_Syntax_Syntax.Tm_app uu____66186  in
            mk1 uu____66185
          else
            (let uu____66274 =
               let uu____66280 =
                 let uu____66282 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____66282
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____66280)  in
             FStar_Errors.raise_err uu____66274)
      | FStar_Syntax_Syntax.Tm_bvar uu____66286 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____66287 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____66288 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____66289 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____66317 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____66317 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_66325 = env  in
                 let uu____66326 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____66326;
                   subst = (uu___1110_66325.subst);
                   tc_const = (uu___1110_66325.tc_const)
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
               ((let uu___1125_66353 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_66353.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_66353.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____66360 =
            let uu____66361 =
              let uu____66368 = star_type' env t2  in (uu____66368, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____66361  in
          mk1 uu____66360
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____66420 =
            let uu____66421 =
              let uu____66448 = star_type' env e  in
              let uu____66451 =
                let uu____66468 =
                  let uu____66477 = star_type' env t2  in
                  FStar_Util.Inl uu____66477  in
                (uu____66468, FStar_Pervasives_Native.None)  in
              (uu____66448, uu____66451, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66421  in
          mk1 uu____66420
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____66565 =
            let uu____66566 =
              let uu____66593 = star_type' env e  in
              let uu____66596 =
                let uu____66613 =
                  let uu____66622 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____66622  in
                (uu____66613, FStar_Pervasives_Native.None)  in
              (uu____66593, uu____66596, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66566  in
          mk1 uu____66565
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____66663,(uu____66664,FStar_Pervasives_Native.Some uu____66665),uu____66666)
          ->
          let uu____66715 =
            let uu____66721 =
              let uu____66723 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____66723
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66721)  in
          FStar_Errors.raise_err uu____66715
      | FStar_Syntax_Syntax.Tm_refine uu____66727 ->
          let uu____66734 =
            let uu____66740 =
              let uu____66742 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____66742
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66740)  in
          FStar_Errors.raise_err uu____66734
      | FStar_Syntax_Syntax.Tm_uinst uu____66746 ->
          let uu____66753 =
            let uu____66759 =
              let uu____66761 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____66761
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66759)  in
          FStar_Errors.raise_err uu____66753
      | FStar_Syntax_Syntax.Tm_quoted uu____66765 ->
          let uu____66772 =
            let uu____66778 =
              let uu____66780 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____66780
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66778)  in
          FStar_Errors.raise_err uu____66772
      | FStar_Syntax_Syntax.Tm_constant uu____66784 ->
          let uu____66785 =
            let uu____66791 =
              let uu____66793 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____66793
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66791)  in
          FStar_Errors.raise_err uu____66785
      | FStar_Syntax_Syntax.Tm_match uu____66797 ->
          let uu____66820 =
            let uu____66826 =
              let uu____66828 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____66828
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66826)  in
          FStar_Errors.raise_err uu____66820
      | FStar_Syntax_Syntax.Tm_let uu____66832 ->
          let uu____66846 =
            let uu____66852 =
              let uu____66854 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____66854
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66852)  in
          FStar_Errors.raise_err uu____66846
      | FStar_Syntax_Syntax.Tm_uvar uu____66858 ->
          let uu____66871 =
            let uu____66877 =
              let uu____66879 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____66879
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66877)  in
          FStar_Errors.raise_err uu____66871
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____66883 =
            let uu____66889 =
              let uu____66891 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____66891
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66889)  in
          FStar_Errors.raise_err uu____66883
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66896 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____66896
      | FStar_Syntax_Syntax.Tm_delayed uu____66899 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_66931  ->
    match uu___588_66931 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_66942  ->
                match uu___587_66942 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____66945 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____66955 =
      let uu____66956 = FStar_Syntax_Subst.compress t  in
      uu____66956.FStar_Syntax_Syntax.n  in
    match uu____66955 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____66988 =
            let uu____66989 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____66989  in
          is_C uu____66988  in
        if r
        then
          ((let uu____67013 =
              let uu____67015 =
                FStar_List.for_all
                  (fun uu____67026  ->
                     match uu____67026 with | (h,uu____67035) -> is_C h) args
                 in
              Prims.op_Negation uu____67015  in
            if uu____67013 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____67048 =
              let uu____67050 =
                FStar_List.for_all
                  (fun uu____67062  ->
                     match uu____67062 with
                     | (h,uu____67071) ->
                         let uu____67076 = is_C h  in
                         Prims.op_Negation uu____67076) args
                 in
              Prims.op_Negation uu____67050  in
            if uu____67048 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____67105 = nm_of_comp comp  in
        (match uu____67105 with
         | M t1 ->
             ((let uu____67109 = is_C t1  in
               if uu____67109 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____67118) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____67124) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____67130,uu____67131) -> is_C t1
    | uu____67172 -> false
  
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
          let uu____67208 =
            let uu____67209 =
              let uu____67226 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____67229 =
                let uu____67240 =
                  let uu____67249 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____67249)  in
                [uu____67240]  in
              (uu____67226, uu____67229)  in
            FStar_Syntax_Syntax.Tm_app uu____67209  in
          mk1 uu____67208  in
        let uu____67285 =
          let uu____67286 = FStar_Syntax_Syntax.mk_binder p  in [uu____67286]
           in
        FStar_Syntax_Util.abs uu____67285 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_67311  ->
    match uu___589_67311 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____67314 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____67552 =
          match uu____67552 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____67589 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____67592 =
                       let uu____67594 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____67594  in
                     Prims.op_Negation uu____67592)
                   in
                if uu____67589
                then
                  let uu____67596 =
                    let uu____67602 =
                      let uu____67604 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____67606 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____67608 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____67604 uu____67606 uu____67608
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____67602)  in
                  FStar_Errors.raise_err uu____67596
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____67633 = mk_return env t1 s_e  in
                     ((M t1), uu____67633, u_e)))
               | (M t1,N t2) ->
                   let uu____67640 =
                     let uu____67646 =
                       let uu____67648 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____67650 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____67652 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____67648 uu____67650 uu____67652
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____67646)
                      in
                   FStar_Errors.raise_err uu____67640)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_67704 =
            match uu___590_67704 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____67720 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____67741 =
                let uu____67747 =
                  let uu____67749 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____67749
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____67747)  in
              FStar_Errors.raise_error uu____67741 e2.FStar_Syntax_Syntax.pos
          | M uu____67759 ->
              let uu____67760 = check env1 e2 context_nm  in
              strip_m uu____67760
           in
        let uu____67767 =
          let uu____67768 = FStar_Syntax_Subst.compress e  in
          uu____67768.FStar_Syntax_Syntax.n  in
        match uu____67767 with
        | FStar_Syntax_Syntax.Tm_bvar uu____67777 ->
            let uu____67778 = infer env e  in return_if uu____67778
        | FStar_Syntax_Syntax.Tm_name uu____67785 ->
            let uu____67786 = infer env e  in return_if uu____67786
        | FStar_Syntax_Syntax.Tm_fvar uu____67793 ->
            let uu____67794 = infer env e  in return_if uu____67794
        | FStar_Syntax_Syntax.Tm_abs uu____67801 ->
            let uu____67820 = infer env e  in return_if uu____67820
        | FStar_Syntax_Syntax.Tm_constant uu____67827 ->
            let uu____67828 = infer env e  in return_if uu____67828
        | FStar_Syntax_Syntax.Tm_quoted uu____67835 ->
            let uu____67842 = infer env e  in return_if uu____67842
        | FStar_Syntax_Syntax.Tm_app uu____67849 ->
            let uu____67866 = infer env e  in return_if uu____67866
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____67874 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____67874 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____67939) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____67945) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____67951,uu____67952) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____67993 ->
            let uu____68007 =
              let uu____68009 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____68009  in
            failwith uu____68007
        | FStar_Syntax_Syntax.Tm_type uu____68018 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____68026 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____68048 ->
            let uu____68055 =
              let uu____68057 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____68057  in
            failwith uu____68055
        | FStar_Syntax_Syntax.Tm_uvar uu____68066 ->
            let uu____68079 =
              let uu____68081 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____68081  in
            failwith uu____68079
        | FStar_Syntax_Syntax.Tm_delayed uu____68090 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____68120 =
              let uu____68122 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____68122  in
            failwith uu____68120

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
      let uu____68152 =
        let uu____68153 = FStar_Syntax_Subst.compress e  in
        uu____68153.FStar_Syntax_Syntax.n  in
      match uu____68152 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____68172 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____68172
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____68223;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____68224;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____68230 =
                  let uu___1360_68231 = rc  in
                  let uu____68232 =
                    let uu____68237 =
                      let uu____68240 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____68240  in
                    FStar_Pervasives_Native.Some uu____68237  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_68231.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____68232;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_68231.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____68230
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_68252 = env  in
            let uu____68253 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____68253;
              subst = (uu___1366_68252.subst);
              tc_const = (uu___1366_68252.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____68279  ->
                 match uu____68279 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_68302 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_68302.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_68302.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____68303 =
            FStar_List.fold_left
              (fun uu____68334  ->
                 fun uu____68335  ->
                   match (uu____68334, uu____68335) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____68393 = is_C c  in
                       if uu____68393
                       then
                         let xw =
                           let uu____68403 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____68403
                            in
                         let x =
                           let uu___1385_68406 = bv  in
                           let uu____68407 =
                             let uu____68410 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____68410  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_68406.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_68406.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____68407
                           }  in
                         let env3 =
                           let uu___1388_68412 = env2  in
                           let uu____68413 =
                             let uu____68416 =
                               let uu____68417 =
                                 let uu____68424 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____68424)  in
                               FStar_Syntax_Syntax.NT uu____68417  in
                             uu____68416 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_68412.tcenv);
                             subst = uu____68413;
                             tc_const = (uu___1388_68412.tc_const)
                           }  in
                         let uu____68429 =
                           let uu____68432 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____68433 =
                             let uu____68436 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____68436 :: acc  in
                           uu____68432 :: uu____68433  in
                         (env3, uu____68429)
                       else
                         (let x =
                            let uu___1391_68442 = bv  in
                            let uu____68443 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_68442.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_68442.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____68443
                            }  in
                          let uu____68446 =
                            let uu____68449 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____68449 :: acc  in
                          (env2, uu____68446))) (env1, []) binders1
             in
          (match uu____68303 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____68469 =
                 let check_what =
                   let uu____68495 = is_monadic rc_opt1  in
                   if uu____68495 then check_m else check_n  in
                 let uu____68512 = check_what env2 body1  in
                 match uu____68512 with
                 | (t,s_body,u_body) ->
                     let uu____68532 =
                       let uu____68535 =
                         let uu____68536 = is_monadic rc_opt1  in
                         if uu____68536 then M t else N t  in
                       comp_of_nm uu____68535  in
                     (uu____68532, s_body, u_body)
                  in
               (match uu____68469 with
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
                                 let uu____68576 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_68582  ->
                                           match uu___591_68582 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____68585 -> false))
                                    in
                                 if uu____68576
                                 then
                                   let uu____68588 =
                                     FStar_List.filter
                                       (fun uu___592_68592  ->
                                          match uu___592_68592 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____68595 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____68588
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____68606 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_68612  ->
                                         match uu___593_68612 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____68615 -> false))
                                  in
                               if uu____68606
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_68624  ->
                                        match uu___594_68624 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____68627 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____68629 =
                                   let uu____68630 =
                                     let uu____68635 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____68635
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____68630 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____68629
                               else
                                 (let uu____68642 =
                                    let uu___1432_68643 = rc  in
                                    let uu____68644 =
                                      let uu____68649 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____68649
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_68643.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____68644;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_68643.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____68642))
                       in
                    let uu____68654 =
                      let comp1 =
                        let uu____68662 = is_monadic rc_opt1  in
                        let uu____68664 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____68662 uu____68664
                         in
                      let uu____68665 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____68665,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____68654 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____68703 =
                             let uu____68704 =
                               let uu____68723 =
                                 let uu____68726 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____68726 s_rc_opt  in
                               (s_binders1, s_body1, uu____68723)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68704  in
                           mk1 uu____68703  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____68746 =
                             let uu____68747 =
                               let uu____68766 =
                                 let uu____68769 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____68769 u_rc_opt  in
                               (u_binders2, u_body2, uu____68766)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68747  in
                           mk1 uu____68746  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____68785;_};
            FStar_Syntax_Syntax.fv_delta = uu____68786;
            FStar_Syntax_Syntax.fv_qual = uu____68787;_}
          ->
          let uu____68790 =
            let uu____68795 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____68795  in
          (match uu____68790 with
           | (uu____68826,t) ->
               let uu____68828 =
                 let uu____68829 = normalize1 t  in N uu____68829  in
               (uu____68828, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____68830;
             FStar_Syntax_Syntax.vars = uu____68831;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____68910 = FStar_Syntax_Util.head_and_args e  in
          (match uu____68910 with
           | (unary_op1,uu____68934) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69005;
             FStar_Syntax_Syntax.vars = uu____69006;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____69102 = FStar_Syntax_Util.head_and_args e  in
          (match uu____69102 with
           | (unary_op1,uu____69126) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69205;
             FStar_Syntax_Syntax.vars = uu____69206;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____69244 = infer env a  in
          (match uu____69244 with
           | (t,s,u) ->
               let uu____69260 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69260 with
                | (head1,uu____69284) ->
                    let uu____69309 =
                      let uu____69310 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____69310  in
                    let uu____69311 =
                      let uu____69312 =
                        let uu____69313 =
                          let uu____69330 =
                            let uu____69341 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69341]  in
                          (head1, uu____69330)  in
                        FStar_Syntax_Syntax.Tm_app uu____69313  in
                      mk1 uu____69312  in
                    let uu____69378 =
                      let uu____69379 =
                        let uu____69380 =
                          let uu____69397 =
                            let uu____69408 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69408]  in
                          (head1, uu____69397)  in
                        FStar_Syntax_Syntax.Tm_app uu____69380  in
                      mk1 uu____69379  in
                    (uu____69309, uu____69311, uu____69378)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69445;
             FStar_Syntax_Syntax.vars = uu____69446;_},(a1,uu____69448)::a2::[])
          ->
          let uu____69504 = infer env a1  in
          (match uu____69504 with
           | (t,s,u) ->
               let uu____69520 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69520 with
                | (head1,uu____69544) ->
                    let uu____69569 =
                      let uu____69570 =
                        let uu____69571 =
                          let uu____69588 =
                            let uu____69599 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69599; a2]  in
                          (head1, uu____69588)  in
                        FStar_Syntax_Syntax.Tm_app uu____69571  in
                      mk1 uu____69570  in
                    let uu____69644 =
                      let uu____69645 =
                        let uu____69646 =
                          let uu____69663 =
                            let uu____69674 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69674; a2]  in
                          (head1, uu____69663)  in
                        FStar_Syntax_Syntax.Tm_app uu____69646  in
                      mk1 uu____69645  in
                    (t, uu____69569, uu____69644)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69719;
             FStar_Syntax_Syntax.vars = uu____69720;_},uu____69721)
          ->
          let uu____69746 =
            let uu____69752 =
              let uu____69754 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69754
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69752)  in
          FStar_Errors.raise_error uu____69746 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69764;
             FStar_Syntax_Syntax.vars = uu____69765;_},uu____69766)
          ->
          let uu____69791 =
            let uu____69797 =
              let uu____69799 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69799
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69797)  in
          FStar_Errors.raise_error uu____69791 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____69835 = check_n env head1  in
          (match uu____69835 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____69858 =
                   let uu____69859 = FStar_Syntax_Subst.compress t  in
                   uu____69859.FStar_Syntax_Syntax.n  in
                 match uu____69858 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____69863 -> true
                 | uu____69879 -> false  in
               let rec flatten1 t =
                 let uu____69901 =
                   let uu____69902 = FStar_Syntax_Subst.compress t  in
                   uu____69902.FStar_Syntax_Syntax.n  in
                 match uu____69901 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____69921);
                                FStar_Syntax_Syntax.pos = uu____69922;
                                FStar_Syntax_Syntax.vars = uu____69923;_})
                     when is_arrow t1 ->
                     let uu____69952 = flatten1 t1  in
                     (match uu____69952 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____70052,uu____70053) -> flatten1 e1
                 | uu____70094 ->
                     let uu____70095 =
                       let uu____70101 =
                         let uu____70103 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____70103
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____70101)  in
                     FStar_Errors.raise_err uu____70095
                  in
               let uu____70121 = flatten1 t_head  in
               (match uu____70121 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____70196 =
                          let uu____70202 =
                            let uu____70204 = FStar_Util.string_of_int n1  in
                            let uu____70206 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____70208 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____70204 uu____70206 uu____70208
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____70202)
                           in
                        FStar_Errors.raise_err uu____70196)
                     else ();
                     (let uu____70214 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____70214 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____70267 args1 =
                            match uu____70267 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____70367 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____70367
                                 | (binders3,[]) ->
                                     let uu____70405 =
                                       let uu____70406 =
                                         let uu____70409 =
                                           let uu____70410 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____70410
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____70409
                                          in
                                       uu____70406.FStar_Syntax_Syntax.n  in
                                     (match uu____70405 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____70443 =
                                            let uu____70444 =
                                              let uu____70445 =
                                                let uu____70460 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____70460)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____70445
                                               in
                                            mk1 uu____70444  in
                                          N uu____70443
                                      | uu____70473 -> failwith "wat?")
                                 | ([],uu____70475::uu____70476) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____70529)::binders3,(arg,uu____70532)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____70619 = FStar_List.splitAt n' binders1
                             in
                          (match uu____70619 with
                           | (binders2,uu____70653) ->
                               let uu____70686 =
                                 let uu____70709 =
                                   FStar_List.map2
                                     (fun uu____70771  ->
                                        fun uu____70772  ->
                                          match (uu____70771, uu____70772)
                                          with
                                          | ((bv,uu____70820),(arg,q)) ->
                                              let uu____70849 =
                                                let uu____70850 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____70850.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____70849 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____70871 ->
                                                   let uu____70872 =
                                                     let uu____70879 =
                                                       star_type' env arg  in
                                                     (uu____70879, q)  in
                                                   (uu____70872, [(arg, q)])
                                               | uu____70916 ->
                                                   let uu____70917 =
                                                     check_n env arg  in
                                                   (match uu____70917 with
                                                    | (uu____70942,s_arg,u_arg)
                                                        ->
                                                        let uu____70945 =
                                                          let uu____70954 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____70954
                                                          then
                                                            let uu____70965 =
                                                              let uu____70972
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____70972,
                                                                q)
                                                               in
                                                            [uu____70965;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____70945))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____70709  in
                               (match uu____70686 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____71100 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____71113 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____71100, uu____71113)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____71182) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____71188) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____71194,uu____71195) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____71237 =
            let uu____71238 = env.tc_const c  in N uu____71238  in
          (uu____71237, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____71245 ->
          let uu____71259 =
            let uu____71261 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____71261  in
          failwith uu____71259
      | FStar_Syntax_Syntax.Tm_type uu____71270 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____71278 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____71300 ->
          let uu____71307 =
            let uu____71309 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____71309  in
          failwith uu____71307
      | FStar_Syntax_Syntax.Tm_uvar uu____71318 ->
          let uu____71331 =
            let uu____71333 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____71333  in
          failwith uu____71331
      | FStar_Syntax_Syntax.Tm_delayed uu____71342 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71372 =
            let uu____71374 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____71374  in
          failwith uu____71372

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
          let uu____71423 = check_n env e0  in
          match uu____71423 with
          | (uu____71436,s_e0,u_e0) ->
              let uu____71439 =
                let uu____71468 =
                  FStar_List.map
                    (fun b  ->
                       let uu____71529 = FStar_Syntax_Subst.open_branch b  in
                       match uu____71529 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_71571 = env  in
                             let uu____71572 =
                               let uu____71573 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____71573
                                in
                             {
                               tcenv = uu____71572;
                               subst = (uu___1707_71571.subst);
                               tc_const = (uu___1707_71571.tc_const)
                             }  in
                           let uu____71576 = f env1 body  in
                           (match uu____71576 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____71648 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____71468  in
              (match uu____71439 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____71754 = FStar_List.hd nms  in
                     match uu____71754 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_71763  ->
                          match uu___595_71763 with
                          | M uu____71765 -> true
                          | uu____71767 -> false) nms
                      in
                   let uu____71769 =
                     let uu____71806 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____71896  ->
                              match uu____71896 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____72080 =
                                         check env original_body (M t2)  in
                                       (match uu____72080 with
                                        | (uu____72117,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____72156,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____71806  in
                   (match uu____71769 with
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
                              (fun uu____72345  ->
                                 match uu____72345 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____72396 =
                                         let uu____72397 =
                                           let uu____72414 =
                                             let uu____72425 =
                                               let uu____72434 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____72437 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____72434, uu____72437)  in
                                             [uu____72425]  in
                                           (s_body, uu____72414)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____72397
                                          in
                                       mk1 uu____72396  in
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
                            let uu____72572 =
                              let uu____72573 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____72573]  in
                            let uu____72592 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____72572 uu____72592
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____72616 =
                              let uu____72625 =
                                let uu____72632 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____72632
                                 in
                              [uu____72625]  in
                            let uu____72651 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____72616 uu____72651
                             in
                          let uu____72654 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____72693 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____72654, uu____72693)
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
                           let uu____72803 =
                             let uu____72804 =
                               let uu____72805 =
                                 let uu____72832 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____72832,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____72805
                                in
                             mk1 uu____72804  in
                           let uu____72891 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____72803, uu____72891))))

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
              let uu____72956 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____72956]  in
            let uu____72975 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____72975 with
            | (x_binders1,e21) ->
                let uu____72988 = infer env e1  in
                (match uu____72988 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____73005 = is_C t1  in
                       if uu____73005
                       then
                         let uu___1793_73008 = binding  in
                         let uu____73009 =
                           let uu____73012 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____73012  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_73008.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_73008.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____73009;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_73008.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_73008.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_73008.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_73008.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_73016 = env  in
                       let uu____73017 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_73019 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_73019.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_73019.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73017;
                         subst = (uu___1796_73016.subst);
                         tc_const = (uu___1796_73016.tc_const)
                       }  in
                     let uu____73020 = proceed env1 e21  in
                     (match uu____73020 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_73037 = binding  in
                            let uu____73038 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_73037.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_73037.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____73038;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_73037.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_73037.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_73037.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_73037.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____73041 =
                            let uu____73042 =
                              let uu____73043 =
                                let uu____73057 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_73074 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_73074.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_73074.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_73074.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_73074.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_73074.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_73074.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73057)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73043  in
                            mk1 uu____73042  in
                          let uu____73075 =
                            let uu____73076 =
                              let uu____73077 =
                                let uu____73091 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_73108 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_73108.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_73108.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_73108.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_73108.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_73108.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_73108.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73091)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73077  in
                            mk1 uu____73076  in
                          (nm_rec, uu____73041, uu____73075))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_73113 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_73113.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_73113.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_73113.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_73113.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_73113.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_73115 = env  in
                       let uu____73116 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_73118 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_73118.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_73118.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73116;
                         subst = (uu___1820_73115.subst);
                         tc_const = (uu___1820_73115.tc_const)
                       }  in
                     let uu____73119 = ensure_m env1 e21  in
                     (match uu____73119 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____73143 =
                              let uu____73144 =
                                let uu____73161 =
                                  let uu____73172 =
                                    let uu____73181 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____73184 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____73181, uu____73184)  in
                                  [uu____73172]  in
                                (s_e2, uu____73161)  in
                              FStar_Syntax_Syntax.Tm_app uu____73144  in
                            mk1 uu____73143  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____73226 =
                              let uu____73227 =
                                let uu____73244 =
                                  let uu____73255 =
                                    let uu____73264 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____73264)  in
                                  [uu____73255]  in
                                (s_e1, uu____73244)  in
                              FStar_Syntax_Syntax.Tm_app uu____73227  in
                            mk1 uu____73226  in
                          let uu____73300 =
                            let uu____73301 =
                              let uu____73302 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____73302]  in
                            FStar_Syntax_Util.abs uu____73301 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____73321 =
                            let uu____73322 =
                              let uu____73323 =
                                let uu____73337 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_73354 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_73354.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_73354.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_73354.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_73354.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_73354.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_73354.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73337)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73323  in
                            mk1 uu____73322  in
                          ((M t2), uu____73300, uu____73321)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73364 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____73364  in
      let uu____73365 = check env e mn  in
      match uu____73365 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73381 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73404 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____73404  in
      let uu____73405 = check env e mn  in
      match uu____73405 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73421 -> failwith "[check_m]: impossible"

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
        (let uu____73454 =
           let uu____73456 = is_C c  in Prims.op_Negation uu____73456  in
         if uu____73454 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____73470 =
           let uu____73471 = FStar_Syntax_Subst.compress c  in
           uu____73471.FStar_Syntax_Syntax.n  in
         match uu____73470 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____73500 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____73500 with
              | (wp_head,wp_args) ->
                  ((let uu____73544 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____73563 =
                           let uu____73565 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____73565
                            in
                         Prims.op_Negation uu____73563)
                       in
                    if uu____73544 then failwith "mismatch" else ());
                   (let uu____73578 =
                      let uu____73579 =
                        let uu____73596 =
                          FStar_List.map2
                            (fun uu____73634  ->
                               fun uu____73635  ->
                                 match (uu____73634, uu____73635) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____73697 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____73697
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____73706 =
                                         let uu____73708 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____73708 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____73706
                                       then
                                         let uu____73710 =
                                           let uu____73716 =
                                             let uu____73718 =
                                               print_implicit q  in
                                             let uu____73720 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____73718 uu____73720
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____73716)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____73710
                                       else ());
                                      (let uu____73726 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____73726, q)))) args wp_args
                           in
                        (head1, uu____73596)  in
                      FStar_Syntax_Syntax.Tm_app uu____73579  in
                    mk1 uu____73578)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____73772 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____73772 with
              | (binders_orig,comp1) ->
                  let uu____73779 =
                    let uu____73796 =
                      FStar_List.map
                        (fun uu____73836  ->
                           match uu____73836 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____73864 = is_C h  in
                               if uu____73864
                               then
                                 let w' =
                                   let uu____73880 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____73880
                                    in
                                 let uu____73882 =
                                   let uu____73891 =
                                     let uu____73900 =
                                       let uu____73907 =
                                         let uu____73908 =
                                           let uu____73909 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____73909  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____73908
                                          in
                                       (uu____73907, q)  in
                                     [uu____73900]  in
                                   (w', q) :: uu____73891  in
                                 (w', uu____73882)
                               else
                                 (let x =
                                    let uu____73943 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____73943
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____73796  in
                  (match uu____73779 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____74017 =
                           let uu____74020 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____74020
                            in
                         FStar_Syntax_Subst.subst_comp uu____74017 comp1  in
                       let app =
                         let uu____74024 =
                           let uu____74025 =
                             let uu____74042 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____74061 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____74062 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____74061, uu____74062)) bvs
                                in
                             (wp, uu____74042)  in
                           FStar_Syntax_Syntax.Tm_app uu____74025  in
                         mk1 uu____74024  in
                       let comp3 =
                         let uu____74077 = type_of_comp comp2  in
                         let uu____74078 = is_monadic_comp comp2  in
                         trans_G env uu____74077 uu____74078 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____74081,uu____74082) ->
             trans_F_ env e wp
         | uu____74123 -> failwith "impossible trans_F_")

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
            let uu____74131 =
              let uu____74132 = star_type' env h  in
              let uu____74135 =
                let uu____74146 =
                  let uu____74155 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____74155)  in
                [uu____74146]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____74132;
                FStar_Syntax_Syntax.effect_args = uu____74135;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____74131
          else
            (let uu____74181 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____74181)

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
    fun t  -> let uu____74202 = n env.tcenv t  in star_type' env uu____74202
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____74222 = n env.tcenv t  in check_n env uu____74222
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____74239 = n env.tcenv c  in
        let uu____74240 = n env.tcenv wp  in
        trans_F_ env uu____74239 uu____74240
  