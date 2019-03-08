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
              let uu___613_61009 = a  in
              let uu____61010 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_61009.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_61009.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____61010
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____61023 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____61023
             then
               (d "Elaborating extra WP combinators";
                (let uu____61029 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____61029))
             else ());
            (let rec collect_binders t =
               let uu____61048 =
                 let uu____61049 =
                   let uu____61052 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____61052
                    in
                 uu____61049.FStar_Syntax_Syntax.n  in
               match uu____61048 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____61087) -> t1
                     | uu____61096 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____61098 = collect_binders rest  in
                   FStar_List.append bs uu____61098
               | FStar_Syntax_Syntax.Tm_type uu____61113 -> []
               | uu____61120 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____61147 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____61147
                 FStar_Syntax_Util.name_binders
                in
             (let uu____61173 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____61173
              then
                let uu____61177 =
                  let uu____61179 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____61179  in
                d uu____61177
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____61217 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____61217 with
                | (sigelt,fv) ->
                    ((let uu____61225 =
                        let uu____61228 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____61228
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____61225);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____61308  ->
                     match uu____61308 with
                     | (t,b) ->
                         let uu____61322 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____61322))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____61361 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____61361))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____61395 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____61395)
                 in
              let uu____61398 =
                let uu____61415 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____61440 =
                        let uu____61443 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____61443  in
                      FStar_Syntax_Util.arrow gamma uu____61440  in
                    let uu____61444 =
                      let uu____61445 =
                        let uu____61454 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____61461 =
                          let uu____61470 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____61470]  in
                        uu____61454 :: uu____61461  in
                      FStar_List.append binders uu____61445  in
                    FStar_Syntax_Util.abs uu____61444 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____61501 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____61502 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____61501, uu____61502)  in
                match uu____61415 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____61544 =
                        let uu____61545 =
                          let uu____61562 =
                            let uu____61573 =
                              FStar_List.map
                                (fun uu____61595  ->
                                   match uu____61595 with
                                   | (bv,uu____61607) ->
                                       let uu____61612 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____61613 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____61612, uu____61613)) binders
                               in
                            let uu____61615 =
                              let uu____61622 =
                                let uu____61627 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____61628 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____61627, uu____61628)  in
                              let uu____61630 =
                                let uu____61637 =
                                  let uu____61642 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____61642)  in
                                [uu____61637]  in
                              uu____61622 :: uu____61630  in
                            FStar_List.append uu____61573 uu____61615  in
                          (fv, uu____61562)  in
                        FStar_Syntax_Syntax.Tm_app uu____61545  in
                      mk1 uu____61544  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____61398 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____61715 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____61715
                       in
                    let ret1 =
                      let uu____61720 =
                        let uu____61721 =
                          let uu____61724 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____61724  in
                        FStar_Syntax_Util.residual_tot uu____61721  in
                      FStar_Pervasives_Native.Some uu____61720  in
                    let body =
                      let uu____61728 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____61728 ret1  in
                    let uu____61731 =
                      let uu____61732 = mk_all_implicit binders  in
                      let uu____61739 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____61732 uu____61739  in
                    FStar_Syntax_Util.abs uu____61731 body ret1  in
                  let c_pure1 =
                    let uu____61777 = mk_lid "pure"  in
                    register env1 uu____61777 c_pure  in
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
                      let uu____61787 =
                        let uu____61788 =
                          let uu____61789 =
                            let uu____61798 =
                              let uu____61805 =
                                let uu____61806 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____61806
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____61805  in
                            [uu____61798]  in
                          let uu____61819 =
                            let uu____61822 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____61822  in
                          FStar_Syntax_Util.arrow uu____61789 uu____61819  in
                        mk_gctx uu____61788  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____61787
                       in
                    let r =
                      let uu____61825 =
                        let uu____61826 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____61826  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____61825
                       in
                    let ret1 =
                      let uu____61831 =
                        let uu____61832 =
                          let uu____61835 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____61835  in
                        FStar_Syntax_Util.residual_tot uu____61832  in
                      FStar_Pervasives_Native.Some uu____61831  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____61845 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____61848 =
                          let uu____61859 =
                            let uu____61862 =
                              let uu____61863 =
                                let uu____61864 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____61864
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____61863  in
                            [uu____61862]  in
                          FStar_List.append gamma_as_args uu____61859  in
                        FStar_Syntax_Util.mk_app uu____61845 uu____61848  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____61867 =
                      let uu____61868 = mk_all_implicit binders  in
                      let uu____61875 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____61868 uu____61875  in
                    FStar_Syntax_Util.abs uu____61867 outer_body ret1  in
                  let c_app1 =
                    let uu____61927 = mk_lid "app"  in
                    register env1 uu____61927 c_app  in
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
                      let uu____61939 =
                        let uu____61948 =
                          let uu____61955 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____61955  in
                        [uu____61948]  in
                      let uu____61968 =
                        let uu____61971 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____61971  in
                      FStar_Syntax_Util.arrow uu____61939 uu____61968  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____61975 =
                        let uu____61976 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____61976  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____61975
                       in
                    let ret1 =
                      let uu____61981 =
                        let uu____61982 =
                          let uu____61985 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____61985  in
                        FStar_Syntax_Util.residual_tot uu____61982  in
                      FStar_Pervasives_Native.Some uu____61981  in
                    let uu____61986 =
                      let uu____61987 = mk_all_implicit binders  in
                      let uu____61994 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____61987 uu____61994  in
                    let uu____62045 =
                      let uu____62048 =
                        let uu____62059 =
                          let uu____62062 =
                            let uu____62063 =
                              let uu____62074 =
                                let uu____62077 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____62077]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62074
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62063  in
                          let uu____62086 =
                            let uu____62089 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____62089]  in
                          uu____62062 :: uu____62086  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62059
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62048  in
                    FStar_Syntax_Util.abs uu____61986 uu____62045 ret1  in
                  let c_lift11 =
                    let uu____62099 = mk_lid "lift1"  in
                    register env1 uu____62099 c_lift1  in
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
                      let uu____62113 =
                        let uu____62122 =
                          let uu____62129 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62129  in
                        let uu____62130 =
                          let uu____62139 =
                            let uu____62146 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____62146  in
                          [uu____62139]  in
                        uu____62122 :: uu____62130  in
                      let uu____62165 =
                        let uu____62168 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62168  in
                      FStar_Syntax_Util.arrow uu____62113 uu____62165  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62172 =
                        let uu____62173 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62173  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62172
                       in
                    let a2 =
                      let uu____62176 =
                        let uu____62177 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____62177  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____62176
                       in
                    let ret1 =
                      let uu____62182 =
                        let uu____62183 =
                          let uu____62186 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____62186  in
                        FStar_Syntax_Util.residual_tot uu____62183  in
                      FStar_Pervasives_Native.Some uu____62182  in
                    let uu____62187 =
                      let uu____62188 = mk_all_implicit binders  in
                      let uu____62195 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____62188 uu____62195  in
                    let uu____62260 =
                      let uu____62263 =
                        let uu____62274 =
                          let uu____62277 =
                            let uu____62278 =
                              let uu____62289 =
                                let uu____62292 =
                                  let uu____62293 =
                                    let uu____62304 =
                                      let uu____62307 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____62307]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____62304
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____62293
                                   in
                                let uu____62316 =
                                  let uu____62319 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____62319]  in
                                uu____62292 :: uu____62316  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62289
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____62278  in
                          let uu____62328 =
                            let uu____62331 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____62331]  in
                          uu____62277 :: uu____62328  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62274
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62263  in
                    FStar_Syntax_Util.abs uu____62187 uu____62260 ret1  in
                  let c_lift21 =
                    let uu____62341 = mk_lid "lift2"  in
                    register env1 uu____62341 c_lift2  in
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
                      let uu____62353 =
                        let uu____62362 =
                          let uu____62369 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62369  in
                        [uu____62362]  in
                      let uu____62382 =
                        let uu____62385 =
                          let uu____62386 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62386  in
                        FStar_Syntax_Syntax.mk_Total uu____62385  in
                      FStar_Syntax_Util.arrow uu____62353 uu____62382  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____62392 =
                        let uu____62393 =
                          let uu____62396 =
                            let uu____62397 =
                              let uu____62406 =
                                let uu____62413 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____62413
                                 in
                              [uu____62406]  in
                            let uu____62426 =
                              let uu____62429 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____62429  in
                            FStar_Syntax_Util.arrow uu____62397 uu____62426
                             in
                          mk_ctx uu____62396  in
                        FStar_Syntax_Util.residual_tot uu____62393  in
                      FStar_Pervasives_Native.Some uu____62392  in
                    let e1 =
                      let uu____62431 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____62431
                       in
                    let body =
                      let uu____62436 =
                        let uu____62437 =
                          let uu____62446 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____62446]  in
                        FStar_List.append gamma uu____62437  in
                      let uu____62471 =
                        let uu____62474 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____62477 =
                          let uu____62488 =
                            let uu____62489 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____62489  in
                          let uu____62490 = args_of_binders1 gamma  in
                          uu____62488 :: uu____62490  in
                        FStar_Syntax_Util.mk_app uu____62474 uu____62477  in
                      FStar_Syntax_Util.abs uu____62436 uu____62471 ret1  in
                    let uu____62493 =
                      let uu____62494 = mk_all_implicit binders  in
                      let uu____62501 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____62494 uu____62501  in
                    FStar_Syntax_Util.abs uu____62493 body ret1  in
                  let c_push1 =
                    let uu____62546 = mk_lid "push"  in
                    register env1 uu____62546 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____62573 =
                        let uu____62574 =
                          let uu____62591 = args_of_binders1 binders  in
                          (c, uu____62591)  in
                        FStar_Syntax_Syntax.Tm_app uu____62574  in
                      mk1 uu____62573
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____62620 =
                        let uu____62621 =
                          let uu____62630 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____62637 =
                            let uu____62646 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____62646]  in
                          uu____62630 :: uu____62637  in
                        let uu____62671 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____62621 uu____62671  in
                      FStar_Syntax_Syntax.mk_Total uu____62620  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____62676 =
                      let uu____62677 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____62677  in
                    let uu____62692 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____62697 =
                        let uu____62700 =
                          let uu____62711 =
                            let uu____62714 =
                              let uu____62715 =
                                let uu____62726 =
                                  let uu____62735 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____62735  in
                                [uu____62726]  in
                              FStar_Syntax_Util.mk_app l_ite uu____62715  in
                            [uu____62714]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____62711
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____62700  in
                      FStar_Syntax_Util.ascribe uu____62697
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____62676 uu____62692
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____62779 = mk_lid "wp_if_then_else"  in
                    register env1 uu____62779 wp_if_then_else  in
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
                      let uu____62796 =
                        let uu____62807 =
                          let uu____62810 =
                            let uu____62811 =
                              let uu____62822 =
                                let uu____62825 =
                                  let uu____62826 =
                                    let uu____62837 =
                                      let uu____62846 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62846
                                       in
                                    [uu____62837]  in
                                  FStar_Syntax_Util.mk_app l_and uu____62826
                                   in
                                [uu____62825]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62822
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62811  in
                          let uu____62871 =
                            let uu____62874 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____62874]  in
                          uu____62810 :: uu____62871  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62807
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62796  in
                    let uu____62883 =
                      let uu____62884 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____62884  in
                    FStar_Syntax_Util.abs uu____62883 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____62900 = mk_lid "wp_assert"  in
                    register env1 uu____62900 wp_assert  in
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
                      let uu____62917 =
                        let uu____62928 =
                          let uu____62931 =
                            let uu____62932 =
                              let uu____62943 =
                                let uu____62946 =
                                  let uu____62947 =
                                    let uu____62958 =
                                      let uu____62967 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____62967
                                       in
                                    [uu____62958]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____62947
                                   in
                                [uu____62946]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62943
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62932  in
                          let uu____62992 =
                            let uu____62995 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____62995]  in
                          uu____62931 :: uu____62992  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62928
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62917  in
                    let uu____63004 =
                      let uu____63005 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____63005  in
                    FStar_Syntax_Util.abs uu____63004 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____63021 = mk_lid "wp_assume"  in
                    register env1 uu____63021 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____63034 =
                        let uu____63043 =
                          let uu____63050 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____63050  in
                        [uu____63043]  in
                      let uu____63063 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____63034 uu____63063  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____63071 =
                        let uu____63082 =
                          let uu____63085 =
                            let uu____63086 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____63086  in
                          let uu____63105 =
                            let uu____63108 =
                              let uu____63109 =
                                let uu____63120 =
                                  let uu____63123 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____63123]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____63120
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____63109
                               in
                            [uu____63108]  in
                          uu____63085 :: uu____63105  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63082
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63071  in
                    let uu____63140 =
                      let uu____63141 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____63141  in
                    FStar_Syntax_Util.abs uu____63140 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____63157 = mk_lid "wp_close"  in
                    register env1 uu____63157 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____63168 =
                      let uu____63169 =
                        let uu____63170 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____63170
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____63169
                       in
                    FStar_Pervasives_Native.Some uu____63168  in
                  let mk_forall1 x body =
                    let uu____63182 =
                      let uu____63189 =
                        let uu____63190 =
                          let uu____63207 =
                            let uu____63218 =
                              let uu____63227 =
                                let uu____63228 =
                                  let uu____63229 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____63229]  in
                                FStar_Syntax_Util.abs uu____63228 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____63227  in
                            [uu____63218]  in
                          (FStar_Syntax_Util.tforall, uu____63207)  in
                        FStar_Syntax_Syntax.Tm_app uu____63190  in
                      FStar_Syntax_Syntax.mk uu____63189  in
                    uu____63182 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____63287 =
                      let uu____63288 = FStar_Syntax_Subst.compress t  in
                      uu____63288.FStar_Syntax_Syntax.n  in
                    match uu____63287 with
                    | FStar_Syntax_Syntax.Tm_type uu____63292 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63325  ->
                              match uu____63325 with
                              | (b,uu____63334) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____63339 -> true  in
                  let rec is_monotonic t =
                    let uu____63352 =
                      let uu____63353 = FStar_Syntax_Subst.compress t  in
                      uu____63353.FStar_Syntax_Syntax.n  in
                    match uu____63352 with
                    | FStar_Syntax_Syntax.Tm_type uu____63357 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____63390  ->
                              match uu____63390 with
                              | (b,uu____63399) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____63404 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____63478 =
                      let uu____63479 = FStar_Syntax_Subst.compress t1  in
                      uu____63479.FStar_Syntax_Syntax.n  in
                    match uu____63478 with
                    | FStar_Syntax_Syntax.Tm_type uu____63484 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____63487);
                                      FStar_Syntax_Syntax.pos = uu____63488;
                                      FStar_Syntax_Syntax.vars = uu____63489;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63533 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63533
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63543 =
                              let uu____63546 =
                                let uu____63557 =
                                  let uu____63566 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63566  in
                                [uu____63557]  in
                              FStar_Syntax_Util.mk_app x uu____63546  in
                            let uu____63583 =
                              let uu____63586 =
                                let uu____63597 =
                                  let uu____63606 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63606  in
                                [uu____63597]  in
                              FStar_Syntax_Util.mk_app y uu____63586  in
                            mk_rel1 b uu____63543 uu____63583  in
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
                             let uu____63630 =
                               let uu____63633 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63636 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63633 uu____63636  in
                             let uu____63639 =
                               let uu____63642 =
                                 let uu____63645 =
                                   let uu____63656 =
                                     let uu____63665 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63665
                                      in
                                   [uu____63656]  in
                                 FStar_Syntax_Util.mk_app x uu____63645  in
                               let uu____63682 =
                                 let uu____63685 =
                                   let uu____63696 =
                                     let uu____63705 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63705
                                      in
                                   [uu____63696]  in
                                 FStar_Syntax_Util.mk_app y uu____63685  in
                               mk_rel1 b uu____63642 uu____63682  in
                             FStar_Syntax_Util.mk_imp uu____63630 uu____63639
                              in
                           let uu____63722 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63722)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____63725);
                                      FStar_Syntax_Syntax.pos = uu____63726;
                                      FStar_Syntax_Syntax.vars = uu____63727;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____63771 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____63771
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____63781 =
                              let uu____63784 =
                                let uu____63795 =
                                  let uu____63804 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63804  in
                                [uu____63795]  in
                              FStar_Syntax_Util.mk_app x uu____63784  in
                            let uu____63821 =
                              let uu____63824 =
                                let uu____63835 =
                                  let uu____63844 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____63844  in
                                [uu____63835]  in
                              FStar_Syntax_Util.mk_app y uu____63824  in
                            mk_rel1 b uu____63781 uu____63821  in
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
                             let uu____63868 =
                               let uu____63871 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____63874 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____63871 uu____63874  in
                             let uu____63877 =
                               let uu____63880 =
                                 let uu____63883 =
                                   let uu____63894 =
                                     let uu____63903 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____63903
                                      in
                                   [uu____63894]  in
                                 FStar_Syntax_Util.mk_app x uu____63883  in
                               let uu____63920 =
                                 let uu____63923 =
                                   let uu____63934 =
                                     let uu____63943 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____63943
                                      in
                                   [uu____63934]  in
                                 FStar_Syntax_Util.mk_app y uu____63923  in
                               mk_rel1 b uu____63880 uu____63920  in
                             FStar_Syntax_Util.mk_imp uu____63868 uu____63877
                              in
                           let uu____63960 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____63960)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_63999 = t1  in
                          let uu____64000 =
                            let uu____64001 =
                              let uu____64016 =
                                let uu____64019 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____64019  in
                              ([binder], uu____64016)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____64001  in
                          {
                            FStar_Syntax_Syntax.n = uu____64000;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_63999.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_63999.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____64042 ->
                        failwith "unhandled arrow"
                    | uu____64060 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____64097 =
                        let uu____64098 = FStar_Syntax_Subst.compress t1  in
                        uu____64098.FStar_Syntax_Syntax.n  in
                      match uu____64097 with
                      | FStar_Syntax_Syntax.Tm_type uu____64101 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____64128 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____64128
                          ->
                          let project i tuple =
                            let projector =
                              let uu____64149 =
                                let uu____64150 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____64150 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____64149
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____64180 =
                            let uu____64191 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____64209  ->
                                     match uu____64209 with
                                     | (t2,q) ->
                                         let uu____64229 = project i x  in
                                         let uu____64232 = project i y  in
                                         mk_stronger t2 uu____64229
                                           uu____64232) args
                               in
                            match uu____64191 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____64180 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____64286);
                                      FStar_Syntax_Syntax.pos = uu____64287;
                                      FStar_Syntax_Syntax.vars = uu____64288;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64332  ->
                                   match uu____64332 with
                                   | (bv,q) ->
                                       let uu____64346 =
                                         let uu____64348 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64348  in
                                       FStar_Syntax_Syntax.gen_bv uu____64346
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64357 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64357) bvs
                             in
                          let body =
                            let uu____64359 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64362 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64359 uu____64362  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____64371);
                                      FStar_Syntax_Syntax.pos = uu____64372;
                                      FStar_Syntax_Syntax.vars = uu____64373;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____64417  ->
                                   match uu____64417 with
                                   | (bv,q) ->
                                       let uu____64431 =
                                         let uu____64433 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____64433  in
                                       FStar_Syntax_Syntax.gen_bv uu____64431
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____64442 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____64442) bvs
                             in
                          let body =
                            let uu____64444 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____64447 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____64444 uu____64447  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____64454 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____64457 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____64460 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____64463 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____64457 uu____64460 uu____64463  in
                    let uu____64466 =
                      let uu____64467 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____64467  in
                    FStar_Syntax_Util.abs uu____64466 body ret_tot_type  in
                  let stronger1 =
                    let uu____64509 = mk_lid "stronger"  in
                    register env1 uu____64509 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64517 = FStar_Util.prefix gamma  in
                    match uu____64517 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____64583 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____64583
                             in
                          let uu____64588 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____64588 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____64598 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____64598  in
                              let guard_free1 =
                                let uu____64610 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____64610  in
                              let pat =
                                let uu____64614 =
                                  let uu____64625 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____64625]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____64614
                                 in
                              let pattern_guarded_body =
                                let uu____64653 =
                                  let uu____64654 =
                                    let uu____64661 =
                                      let uu____64662 =
                                        let uu____64675 =
                                          let uu____64686 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____64686]  in
                                        [uu____64675]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____64662
                                       in
                                    (body, uu____64661)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____64654  in
                                mk1 uu____64653  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____64733 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____64742 =
                            let uu____64745 =
                              let uu____64746 =
                                let uu____64749 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____64752 =
                                  let uu____64763 = args_of_binders1 wp_args
                                     in
                                  let uu____64766 =
                                    let uu____64769 =
                                      let uu____64770 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____64770
                                       in
                                    [uu____64769]  in
                                  FStar_List.append uu____64763 uu____64766
                                   in
                                FStar_Syntax_Util.mk_app uu____64749
                                  uu____64752
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____64746  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____64745
                             in
                          FStar_Syntax_Util.abs gamma uu____64742
                            ret_gtot_type
                           in
                        let uu____64771 =
                          let uu____64772 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____64772  in
                        FStar_Syntax_Util.abs uu____64771 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____64788 = mk_lid "ite_wp"  in
                    register env1 uu____64788 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____64796 = FStar_Util.prefix gamma  in
                    match uu____64796 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____64854 =
                            let uu____64855 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____64862 =
                              let uu____64873 =
                                let uu____64882 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____64882  in
                              [uu____64873]  in
                            FStar_Syntax_Util.mk_app uu____64855 uu____64862
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____64854
                           in
                        let uu____64899 =
                          let uu____64900 =
                            let uu____64909 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____64909 gamma  in
                          FStar_List.append binders uu____64900  in
                        FStar_Syntax_Util.abs uu____64899 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____64931 = mk_lid "null_wp"  in
                    register env1 uu____64931 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____64944 =
                        let uu____64955 =
                          let uu____64958 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____64959 =
                            let uu____64962 =
                              let uu____64963 =
                                let uu____64974 =
                                  let uu____64983 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____64983  in
                                [uu____64974]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____64963
                               in
                            let uu____65000 =
                              let uu____65003 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____65003]  in
                            uu____64962 :: uu____65000  in
                          uu____64958 :: uu____64959  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____64955
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____64944  in
                    let uu____65012 =
                      let uu____65013 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____65013  in
                    FStar_Syntax_Util.abs uu____65012 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____65029 = mk_lid "wp_trivial"  in
                    register env1 uu____65029 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____65035 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____65035
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____65047 =
                      let uu____65048 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____65048  in
                    let uu____65074 =
                      let uu___934_65075 = ed  in
                      let uu____65076 =
                        let uu____65077 = c wp_if_then_else2  in
                        ([], uu____65077)  in
                      let uu____65084 =
                        let uu____65085 = c ite_wp2  in ([], uu____65085)  in
                      let uu____65092 =
                        let uu____65093 = c stronger2  in ([], uu____65093)
                         in
                      let uu____65100 =
                        let uu____65101 = c wp_close2  in ([], uu____65101)
                         in
                      let uu____65108 =
                        let uu____65109 = c wp_assert2  in ([], uu____65109)
                         in
                      let uu____65116 =
                        let uu____65117 = c wp_assume2  in ([], uu____65117)
                         in
                      let uu____65124 =
                        let uu____65125 = c null_wp2  in ([], uu____65125)
                         in
                      let uu____65132 =
                        let uu____65133 = c wp_trivial2  in ([], uu____65133)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_65075.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_65075.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_65075.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_65075.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_65075.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_65075.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_65075.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____65076;
                        FStar_Syntax_Syntax.ite_wp = uu____65084;
                        FStar_Syntax_Syntax.stronger = uu____65092;
                        FStar_Syntax_Syntax.close_wp = uu____65100;
                        FStar_Syntax_Syntax.assert_p = uu____65108;
                        FStar_Syntax_Syntax.assume_p = uu____65116;
                        FStar_Syntax_Syntax.null_wp = uu____65124;
                        FStar_Syntax_Syntax.trivial = uu____65132;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_65075.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_65075.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_65075.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_65075.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_65075.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____65047, uu____65074)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_65157 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_65157.subst);
        tc_const = (uu___939_65157.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____65178 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____65197 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65217) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_65231  ->
                match uu___585_65231 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____65234 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____65236 ->
        let uu____65237 =
          let uu____65243 =
            let uu____65245 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____65245
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____65243)  in
        FStar_Errors.raise_error uu____65237 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_65255  ->
    match uu___586_65255 with
    | N t ->
        let uu____65258 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____65258
    | M t ->
        let uu____65262 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____65262
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____65271,c) -> nm_of_comp c
    | uu____65293 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____65306 = nm_of_comp c  in
    match uu____65306 with | M uu____65308 -> true | N uu____65310 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____65321 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____65337 =
        let uu____65346 =
          let uu____65353 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____65353  in
        [uu____65346]  in
      let uu____65372 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____65337 uu____65372  in
    let uu____65375 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____65375
  
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
        let uu____65417 =
          let uu____65418 =
            let uu____65433 =
              let uu____65442 =
                let uu____65449 =
                  let uu____65450 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____65450  in
                let uu____65451 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____65449, uu____65451)  in
              [uu____65442]  in
            let uu____65469 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____65433, uu____65469)  in
          FStar_Syntax_Syntax.Tm_arrow uu____65418  in
        mk1 uu____65417

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____65509) ->
          let binders1 =
            FStar_List.map
              (fun uu____65555  ->
                 match uu____65555 with
                 | (bv,aqual) ->
                     let uu____65574 =
                       let uu___989_65575 = bv  in
                       let uu____65576 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_65575.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_65575.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____65576
                       }  in
                     (uu____65574, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____65581,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____65583);
                              FStar_Syntax_Syntax.pos = uu____65584;
                              FStar_Syntax_Syntax.vars = uu____65585;_})
               ->
               let uu____65614 =
                 let uu____65615 =
                   let uu____65630 =
                     let uu____65633 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____65633  in
                   (binders1, uu____65630)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____65615  in
               mk1 uu____65614
           | uu____65644 ->
               let uu____65645 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____65645 with
                | N hn ->
                    let uu____65647 =
                      let uu____65648 =
                        let uu____65663 =
                          let uu____65666 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____65666  in
                        (binders1, uu____65663)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65648  in
                    mk1 uu____65647
                | M a ->
                    let uu____65678 =
                      let uu____65679 =
                        let uu____65694 =
                          let uu____65703 =
                            let uu____65712 =
                              let uu____65719 =
                                let uu____65720 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____65720  in
                              let uu____65721 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____65719, uu____65721)  in
                            [uu____65712]  in
                          FStar_List.append binders1 uu____65703  in
                        let uu____65745 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____65694, uu____65745)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____65679  in
                    mk1 uu____65678))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____65839 = f x  in
                    FStar_Util.string_builder_append strb uu____65839);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____65848 = f x1  in
                         FStar_Util.string_builder_append strb uu____65848))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____65852 =
              let uu____65858 =
                let uu____65860 = FStar_Syntax_Print.term_to_string t2  in
                let uu____65862 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____65860 uu____65862
                 in
              (FStar_Errors.Warning_DependencyFound, uu____65858)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____65852  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____65884 =
              let uu____65885 = FStar_Syntax_Subst.compress ty  in
              uu____65885.FStar_Syntax_Syntax.n  in
            match uu____65884 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____65911 =
                  let uu____65913 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____65913  in
                if uu____65911
                then false
                else
                  (try
                     (fun uu___1038_65930  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____65954 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____65954 s  in
                              let uu____65957 =
                                let uu____65959 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____65959  in
                              if uu____65957
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____65965 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____65965 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____65990  ->
                                          match uu____65990 with
                                          | (bv,uu____66002) ->
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
            | uu____66030 ->
                ((let uu____66032 =
                    let uu____66038 =
                      let uu____66040 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____66040
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____66038)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____66032);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____66056 =
              let uu____66057 = FStar_Syntax_Subst.compress head2  in
              uu____66057.FStar_Syntax_Syntax.n  in
            match uu____66056 with
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
                  (let uu____66063 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____66063)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____66066 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____66066 with
                 | ((uu____66076,ty),uu____66078) ->
                     let uu____66083 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____66083
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____66096 =
                         let uu____66097 = FStar_Syntax_Subst.compress res
                            in
                         uu____66097.FStar_Syntax_Syntax.n  in
                       (match uu____66096 with
                        | FStar_Syntax_Syntax.Tm_app uu____66101 -> true
                        | uu____66119 ->
                            ((let uu____66121 =
                                let uu____66127 =
                                  let uu____66129 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____66129
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____66127)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____66121);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____66137 -> true
            | FStar_Syntax_Syntax.Tm_name uu____66139 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____66142) ->
                is_valid_application t2
            | uu____66147 -> false  in
          let uu____66149 = is_valid_application head1  in
          if uu____66149
          then
            let uu____66152 =
              let uu____66153 =
                let uu____66170 =
                  FStar_List.map
                    (fun uu____66199  ->
                       match uu____66199 with
                       | (t2,qual) ->
                           let uu____66224 = star_type' env t2  in
                           (uu____66224, qual)) args
                   in
                (head1, uu____66170)  in
              FStar_Syntax_Syntax.Tm_app uu____66153  in
            mk1 uu____66152
          else
            (let uu____66241 =
               let uu____66247 =
                 let uu____66249 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____66249
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____66247)  in
             FStar_Errors.raise_err uu____66241)
      | FStar_Syntax_Syntax.Tm_bvar uu____66253 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____66254 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____66255 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____66256 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____66284 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____66284 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_66292 = env  in
                 let uu____66293 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____66293;
                   subst = (uu___1110_66292.subst);
                   tc_const = (uu___1110_66292.tc_const)
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
               ((let uu___1125_66320 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_66320.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_66320.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____66327 =
            let uu____66328 =
              let uu____66335 = star_type' env t2  in (uu____66335, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____66328  in
          mk1 uu____66327
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____66387 =
            let uu____66388 =
              let uu____66415 = star_type' env e  in
              let uu____66418 =
                let uu____66435 =
                  let uu____66444 = star_type' env t2  in
                  FStar_Util.Inl uu____66444  in
                (uu____66435, FStar_Pervasives_Native.None)  in
              (uu____66415, uu____66418, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66388  in
          mk1 uu____66387
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____66532 =
            let uu____66533 =
              let uu____66560 = star_type' env e  in
              let uu____66563 =
                let uu____66580 =
                  let uu____66589 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____66589  in
                (uu____66580, FStar_Pervasives_Native.None)  in
              (uu____66560, uu____66563, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____66533  in
          mk1 uu____66532
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____66630,(uu____66631,FStar_Pervasives_Native.Some uu____66632),uu____66633)
          ->
          let uu____66682 =
            let uu____66688 =
              let uu____66690 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____66690
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66688)  in
          FStar_Errors.raise_err uu____66682
      | FStar_Syntax_Syntax.Tm_refine uu____66694 ->
          let uu____66701 =
            let uu____66707 =
              let uu____66709 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____66709
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66707)  in
          FStar_Errors.raise_err uu____66701
      | FStar_Syntax_Syntax.Tm_uinst uu____66713 ->
          let uu____66720 =
            let uu____66726 =
              let uu____66728 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____66728
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66726)  in
          FStar_Errors.raise_err uu____66720
      | FStar_Syntax_Syntax.Tm_quoted uu____66732 ->
          let uu____66739 =
            let uu____66745 =
              let uu____66747 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____66747
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66745)  in
          FStar_Errors.raise_err uu____66739
      | FStar_Syntax_Syntax.Tm_constant uu____66751 ->
          let uu____66752 =
            let uu____66758 =
              let uu____66760 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____66760
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66758)  in
          FStar_Errors.raise_err uu____66752
      | FStar_Syntax_Syntax.Tm_match uu____66764 ->
          let uu____66787 =
            let uu____66793 =
              let uu____66795 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____66795
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66793)  in
          FStar_Errors.raise_err uu____66787
      | FStar_Syntax_Syntax.Tm_let uu____66799 ->
          let uu____66813 =
            let uu____66819 =
              let uu____66821 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____66821
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66819)  in
          FStar_Errors.raise_err uu____66813
      | FStar_Syntax_Syntax.Tm_uvar uu____66825 ->
          let uu____66838 =
            let uu____66844 =
              let uu____66846 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____66846
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66844)  in
          FStar_Errors.raise_err uu____66838
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____66850 =
            let uu____66856 =
              let uu____66858 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____66858
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____66856)  in
          FStar_Errors.raise_err uu____66850
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____66863 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____66863
      | FStar_Syntax_Syntax.Tm_delayed uu____66866 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_66898  ->
    match uu___588_66898 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_66909  ->
                match uu___587_66909 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____66912 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____66922 =
      let uu____66923 = FStar_Syntax_Subst.compress t  in
      uu____66923.FStar_Syntax_Syntax.n  in
    match uu____66922 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____66955 =
            let uu____66956 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____66956  in
          is_C uu____66955  in
        if r
        then
          ((let uu____66980 =
              let uu____66982 =
                FStar_List.for_all
                  (fun uu____66993  ->
                     match uu____66993 with | (h,uu____67002) -> is_C h) args
                 in
              Prims.op_Negation uu____66982  in
            if uu____66980 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____67015 =
              let uu____67017 =
                FStar_List.for_all
                  (fun uu____67029  ->
                     match uu____67029 with
                     | (h,uu____67038) ->
                         let uu____67043 = is_C h  in
                         Prims.op_Negation uu____67043) args
                 in
              Prims.op_Negation uu____67017  in
            if uu____67015 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____67072 = nm_of_comp comp  in
        (match uu____67072 with
         | M t1 ->
             ((let uu____67076 = is_C t1  in
               if uu____67076 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____67085) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____67091) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____67097,uu____67098) -> is_C t1
    | uu____67139 -> false
  
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
          let uu____67175 =
            let uu____67176 =
              let uu____67193 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____67196 =
                let uu____67207 =
                  let uu____67216 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____67216)  in
                [uu____67207]  in
              (uu____67193, uu____67196)  in
            FStar_Syntax_Syntax.Tm_app uu____67176  in
          mk1 uu____67175  in
        let uu____67252 =
          let uu____67253 = FStar_Syntax_Syntax.mk_binder p  in [uu____67253]
           in
        FStar_Syntax_Util.abs uu____67252 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_67278  ->
    match uu___589_67278 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____67281 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____67519 =
          match uu____67519 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____67556 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____67559 =
                       let uu____67561 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____67561  in
                     Prims.op_Negation uu____67559)
                   in
                if uu____67556
                then
                  let uu____67563 =
                    let uu____67569 =
                      let uu____67571 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____67573 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____67575 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____67571 uu____67573 uu____67575
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____67569)  in
                  FStar_Errors.raise_err uu____67563
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____67600 = mk_return env t1 s_e  in
                     ((M t1), uu____67600, u_e)))
               | (M t1,N t2) ->
                   let uu____67607 =
                     let uu____67613 =
                       let uu____67615 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____67617 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____67619 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____67615 uu____67617 uu____67619
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____67613)
                      in
                   FStar_Errors.raise_err uu____67607)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_67671 =
            match uu___590_67671 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____67687 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____67708 =
                let uu____67714 =
                  let uu____67716 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____67716
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____67714)  in
              FStar_Errors.raise_error uu____67708 e2.FStar_Syntax_Syntax.pos
          | M uu____67726 ->
              let uu____67727 = check env1 e2 context_nm  in
              strip_m uu____67727
           in
        let uu____67734 =
          let uu____67735 = FStar_Syntax_Subst.compress e  in
          uu____67735.FStar_Syntax_Syntax.n  in
        match uu____67734 with
        | FStar_Syntax_Syntax.Tm_bvar uu____67744 ->
            let uu____67745 = infer env e  in return_if uu____67745
        | FStar_Syntax_Syntax.Tm_name uu____67752 ->
            let uu____67753 = infer env e  in return_if uu____67753
        | FStar_Syntax_Syntax.Tm_fvar uu____67760 ->
            let uu____67761 = infer env e  in return_if uu____67761
        | FStar_Syntax_Syntax.Tm_abs uu____67768 ->
            let uu____67787 = infer env e  in return_if uu____67787
        | FStar_Syntax_Syntax.Tm_constant uu____67794 ->
            let uu____67795 = infer env e  in return_if uu____67795
        | FStar_Syntax_Syntax.Tm_quoted uu____67802 ->
            let uu____67809 = infer env e  in return_if uu____67809
        | FStar_Syntax_Syntax.Tm_app uu____67816 ->
            let uu____67833 = infer env e  in return_if uu____67833
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____67841 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____67841 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____67906) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____67912) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____67918,uu____67919) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____67960 ->
            let uu____67974 =
              let uu____67976 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____67976  in
            failwith uu____67974
        | FStar_Syntax_Syntax.Tm_type uu____67985 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____67993 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____68015 ->
            let uu____68022 =
              let uu____68024 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____68024  in
            failwith uu____68022
        | FStar_Syntax_Syntax.Tm_uvar uu____68033 ->
            let uu____68046 =
              let uu____68048 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____68048  in
            failwith uu____68046
        | FStar_Syntax_Syntax.Tm_delayed uu____68057 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____68087 =
              let uu____68089 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____68089  in
            failwith uu____68087

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
      let uu____68119 =
        let uu____68120 = FStar_Syntax_Subst.compress e  in
        uu____68120.FStar_Syntax_Syntax.n  in
      match uu____68119 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____68139 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____68139
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____68190;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____68191;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____68197 =
                  let uu___1360_68198 = rc  in
                  let uu____68199 =
                    let uu____68204 =
                      let uu____68207 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____68207  in
                    FStar_Pervasives_Native.Some uu____68204  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_68198.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____68199;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_68198.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____68197
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_68219 = env  in
            let uu____68220 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____68220;
              subst = (uu___1366_68219.subst);
              tc_const = (uu___1366_68219.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____68246  ->
                 match uu____68246 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_68269 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_68269.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_68269.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____68270 =
            FStar_List.fold_left
              (fun uu____68301  ->
                 fun uu____68302  ->
                   match (uu____68301, uu____68302) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____68360 = is_C c  in
                       if uu____68360
                       then
                         let xw =
                           let uu____68370 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____68370
                            in
                         let x =
                           let uu___1385_68373 = bv  in
                           let uu____68374 =
                             let uu____68377 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____68377  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_68373.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_68373.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____68374
                           }  in
                         let env3 =
                           let uu___1388_68379 = env2  in
                           let uu____68380 =
                             let uu____68383 =
                               let uu____68384 =
                                 let uu____68391 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____68391)  in
                               FStar_Syntax_Syntax.NT uu____68384  in
                             uu____68383 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_68379.tcenv);
                             subst = uu____68380;
                             tc_const = (uu___1388_68379.tc_const)
                           }  in
                         let uu____68396 =
                           let uu____68399 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____68400 =
                             let uu____68403 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____68403 :: acc  in
                           uu____68399 :: uu____68400  in
                         (env3, uu____68396)
                       else
                         (let x =
                            let uu___1391_68409 = bv  in
                            let uu____68410 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_68409.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_68409.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____68410
                            }  in
                          let uu____68413 =
                            let uu____68416 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____68416 :: acc  in
                          (env2, uu____68413))) (env1, []) binders1
             in
          (match uu____68270 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____68436 =
                 let check_what =
                   let uu____68462 = is_monadic rc_opt1  in
                   if uu____68462 then check_m else check_n  in
                 let uu____68479 = check_what env2 body1  in
                 match uu____68479 with
                 | (t,s_body,u_body) ->
                     let uu____68499 =
                       let uu____68502 =
                         let uu____68503 = is_monadic rc_opt1  in
                         if uu____68503 then M t else N t  in
                       comp_of_nm uu____68502  in
                     (uu____68499, s_body, u_body)
                  in
               (match uu____68436 with
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
                                 let uu____68543 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_68549  ->
                                           match uu___591_68549 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____68552 -> false))
                                    in
                                 if uu____68543
                                 then
                                   let uu____68555 =
                                     FStar_List.filter
                                       (fun uu___592_68559  ->
                                          match uu___592_68559 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____68562 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____68555
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____68573 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_68579  ->
                                         match uu___593_68579 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____68582 -> false))
                                  in
                               if uu____68573
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_68591  ->
                                        match uu___594_68591 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____68594 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____68596 =
                                   let uu____68597 =
                                     let uu____68602 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____68602
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____68597 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____68596
                               else
                                 (let uu____68609 =
                                    let uu___1432_68610 = rc  in
                                    let uu____68611 =
                                      let uu____68616 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____68616
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_68610.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____68611;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_68610.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____68609))
                       in
                    let uu____68621 =
                      let comp1 =
                        let uu____68629 = is_monadic rc_opt1  in
                        let uu____68631 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____68629 uu____68631
                         in
                      let uu____68632 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____68632,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____68621 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____68670 =
                             let uu____68671 =
                               let uu____68690 =
                                 let uu____68693 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____68693 s_rc_opt  in
                               (s_binders1, s_body1, uu____68690)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68671  in
                           mk1 uu____68670  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____68713 =
                             let uu____68714 =
                               let uu____68733 =
                                 let uu____68736 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____68736 u_rc_opt  in
                               (u_binders2, u_body2, uu____68733)  in
                             FStar_Syntax_Syntax.Tm_abs uu____68714  in
                           mk1 uu____68713  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____68752;_};
            FStar_Syntax_Syntax.fv_delta = uu____68753;
            FStar_Syntax_Syntax.fv_qual = uu____68754;_}
          ->
          let uu____68757 =
            let uu____68762 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____68762  in
          (match uu____68757 with
           | (uu____68793,t) ->
               let uu____68795 =
                 let uu____68796 = normalize1 t  in N uu____68796  in
               (uu____68795, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____68797;
             FStar_Syntax_Syntax.vars = uu____68798;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____68877 = FStar_Syntax_Util.head_and_args e  in
          (match uu____68877 with
           | (unary_op1,uu____68901) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____68972;
             FStar_Syntax_Syntax.vars = uu____68973;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____69069 = FStar_Syntax_Util.head_and_args e  in
          (match uu____69069 with
           | (unary_op1,uu____69093) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69172;
             FStar_Syntax_Syntax.vars = uu____69173;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____69211 = infer env a  in
          (match uu____69211 with
           | (t,s,u) ->
               let uu____69227 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69227 with
                | (head1,uu____69251) ->
                    let uu____69276 =
                      let uu____69277 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____69277  in
                    let uu____69278 =
                      let uu____69279 =
                        let uu____69280 =
                          let uu____69297 =
                            let uu____69308 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69308]  in
                          (head1, uu____69297)  in
                        FStar_Syntax_Syntax.Tm_app uu____69280  in
                      mk1 uu____69279  in
                    let uu____69345 =
                      let uu____69346 =
                        let uu____69347 =
                          let uu____69364 =
                            let uu____69375 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69375]  in
                          (head1, uu____69364)  in
                        FStar_Syntax_Syntax.Tm_app uu____69347  in
                      mk1 uu____69346  in
                    (uu____69276, uu____69278, uu____69345)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69412;
             FStar_Syntax_Syntax.vars = uu____69413;_},(a1,uu____69415)::a2::[])
          ->
          let uu____69471 = infer env a1  in
          (match uu____69471 with
           | (t,s,u) ->
               let uu____69487 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69487 with
                | (head1,uu____69511) ->
                    let uu____69536 =
                      let uu____69537 =
                        let uu____69538 =
                          let uu____69555 =
                            let uu____69566 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____69566; a2]  in
                          (head1, uu____69555)  in
                        FStar_Syntax_Syntax.Tm_app uu____69538  in
                      mk1 uu____69537  in
                    let uu____69611 =
                      let uu____69612 =
                        let uu____69613 =
                          let uu____69630 =
                            let uu____69641 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____69641; a2]  in
                          (head1, uu____69630)  in
                        FStar_Syntax_Syntax.Tm_app uu____69613  in
                      mk1 uu____69612  in
                    (t, uu____69536, uu____69611)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69686;
             FStar_Syntax_Syntax.vars = uu____69687;_},uu____69688)
          ->
          let uu____69713 =
            let uu____69719 =
              let uu____69721 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69721
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69719)  in
          FStar_Errors.raise_error uu____69713 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69731;
             FStar_Syntax_Syntax.vars = uu____69732;_},uu____69733)
          ->
          let uu____69758 =
            let uu____69764 =
              let uu____69766 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____69766
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____69764)  in
          FStar_Errors.raise_error uu____69758 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____69802 = check_n env head1  in
          (match uu____69802 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____69825 =
                   let uu____69826 = FStar_Syntax_Subst.compress t  in
                   uu____69826.FStar_Syntax_Syntax.n  in
                 match uu____69825 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____69830 -> true
                 | uu____69846 -> false  in
               let rec flatten1 t =
                 let uu____69868 =
                   let uu____69869 = FStar_Syntax_Subst.compress t  in
                   uu____69869.FStar_Syntax_Syntax.n  in
                 match uu____69868 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____69888);
                                FStar_Syntax_Syntax.pos = uu____69889;
                                FStar_Syntax_Syntax.vars = uu____69890;_})
                     when is_arrow t1 ->
                     let uu____69919 = flatten1 t1  in
                     (match uu____69919 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____70019,uu____70020) -> flatten1 e1
                 | uu____70061 ->
                     let uu____70062 =
                       let uu____70068 =
                         let uu____70070 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____70070
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____70068)  in
                     FStar_Errors.raise_err uu____70062
                  in
               let uu____70088 = flatten1 t_head  in
               (match uu____70088 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____70163 =
                          let uu____70169 =
                            let uu____70171 = FStar_Util.string_of_int n1  in
                            let uu____70173 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____70175 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____70171 uu____70173 uu____70175
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____70169)
                           in
                        FStar_Errors.raise_err uu____70163)
                     else ();
                     (let uu____70181 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____70181 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____70234 args1 =
                            match uu____70234 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____70334 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____70334
                                 | (binders3,[]) ->
                                     let uu____70372 =
                                       let uu____70373 =
                                         let uu____70376 =
                                           let uu____70377 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____70377
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____70376
                                          in
                                       uu____70373.FStar_Syntax_Syntax.n  in
                                     (match uu____70372 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____70410 =
                                            let uu____70411 =
                                              let uu____70412 =
                                                let uu____70427 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____70427)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____70412
                                               in
                                            mk1 uu____70411  in
                                          N uu____70410
                                      | uu____70440 -> failwith "wat?")
                                 | ([],uu____70442::uu____70443) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____70496)::binders3,(arg,uu____70499)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____70586 = FStar_List.splitAt n' binders1
                             in
                          (match uu____70586 with
                           | (binders2,uu____70620) ->
                               let uu____70653 =
                                 let uu____70676 =
                                   FStar_List.map2
                                     (fun uu____70738  ->
                                        fun uu____70739  ->
                                          match (uu____70738, uu____70739)
                                          with
                                          | ((bv,uu____70787),(arg,q)) ->
                                              let uu____70816 =
                                                let uu____70817 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____70817.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____70816 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____70838 ->
                                                   let uu____70839 =
                                                     let uu____70846 =
                                                       star_type' env arg  in
                                                     (uu____70846, q)  in
                                                   (uu____70839, [(arg, q)])
                                               | uu____70883 ->
                                                   let uu____70884 =
                                                     check_n env arg  in
                                                   (match uu____70884 with
                                                    | (uu____70909,s_arg,u_arg)
                                                        ->
                                                        let uu____70912 =
                                                          let uu____70921 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____70921
                                                          then
                                                            let uu____70932 =
                                                              let uu____70939
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____70939,
                                                                q)
                                                               in
                                                            [uu____70932;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____70912))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____70676  in
                               (match uu____70653 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____71067 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____71080 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____71067, uu____71080)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____71149) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____71155) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____71161,uu____71162) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____71204 =
            let uu____71205 = env.tc_const c  in N uu____71205  in
          (uu____71204, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____71212 ->
          let uu____71226 =
            let uu____71228 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____71228  in
          failwith uu____71226
      | FStar_Syntax_Syntax.Tm_type uu____71237 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____71245 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____71267 ->
          let uu____71274 =
            let uu____71276 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____71276  in
          failwith uu____71274
      | FStar_Syntax_Syntax.Tm_uvar uu____71285 ->
          let uu____71298 =
            let uu____71300 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____71300  in
          failwith uu____71298
      | FStar_Syntax_Syntax.Tm_delayed uu____71309 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71339 =
            let uu____71341 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____71341  in
          failwith uu____71339

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
          let uu____71390 = check_n env e0  in
          match uu____71390 with
          | (uu____71403,s_e0,u_e0) ->
              let uu____71406 =
                let uu____71435 =
                  FStar_List.map
                    (fun b  ->
                       let uu____71496 = FStar_Syntax_Subst.open_branch b  in
                       match uu____71496 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_71538 = env  in
                             let uu____71539 =
                               let uu____71540 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____71540
                                in
                             {
                               tcenv = uu____71539;
                               subst = (uu___1707_71538.subst);
                               tc_const = (uu___1707_71538.tc_const)
                             }  in
                           let uu____71543 = f env1 body  in
                           (match uu____71543 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____71615 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____71435  in
              (match uu____71406 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____71721 = FStar_List.hd nms  in
                     match uu____71721 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_71730  ->
                          match uu___595_71730 with
                          | M uu____71732 -> true
                          | uu____71734 -> false) nms
                      in
                   let uu____71736 =
                     let uu____71773 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____71863  ->
                              match uu____71863 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____72047 =
                                         check env original_body (M t2)  in
                                       (match uu____72047 with
                                        | (uu____72084,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____72123,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____71773  in
                   (match uu____71736 with
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
                              (fun uu____72312  ->
                                 match uu____72312 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____72363 =
                                         let uu____72364 =
                                           let uu____72381 =
                                             let uu____72392 =
                                               let uu____72401 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____72404 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____72401, uu____72404)  in
                                             [uu____72392]  in
                                           (s_body, uu____72381)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____72364
                                          in
                                       mk1 uu____72363  in
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
                            let uu____72539 =
                              let uu____72540 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____72540]  in
                            let uu____72559 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____72539 uu____72559
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____72583 =
                              let uu____72592 =
                                let uu____72599 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____72599
                                 in
                              [uu____72592]  in
                            let uu____72618 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____72583 uu____72618
                             in
                          let uu____72621 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____72660 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____72621, uu____72660)
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
                           let uu____72770 =
                             let uu____72771 =
                               let uu____72772 =
                                 let uu____72799 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____72799,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____72772
                                in
                             mk1 uu____72771  in
                           let uu____72858 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____72770, uu____72858))))

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
              let uu____72923 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____72923]  in
            let uu____72942 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____72942 with
            | (x_binders1,e21) ->
                let uu____72955 = infer env e1  in
                (match uu____72955 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____72972 = is_C t1  in
                       if uu____72972
                       then
                         let uu___1793_72975 = binding  in
                         let uu____72976 =
                           let uu____72979 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____72979  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_72975.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_72975.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____72976;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_72975.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_72975.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_72975.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_72975.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_72983 = env  in
                       let uu____72984 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_72986 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_72986.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_72986.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____72984;
                         subst = (uu___1796_72983.subst);
                         tc_const = (uu___1796_72983.tc_const)
                       }  in
                     let uu____72987 = proceed env1 e21  in
                     (match uu____72987 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_73004 = binding  in
                            let uu____73005 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_73004.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_73004.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____73005;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_73004.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_73004.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_73004.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_73004.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____73008 =
                            let uu____73009 =
                              let uu____73010 =
                                let uu____73024 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_73041 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_73041.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_73041.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_73041.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_73041.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_73041.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_73041.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73024)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73010  in
                            mk1 uu____73009  in
                          let uu____73042 =
                            let uu____73043 =
                              let uu____73044 =
                                let uu____73058 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_73075 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_73075.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_73075.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_73075.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_73075.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_73075.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_73075.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73058)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73044  in
                            mk1 uu____73043  in
                          (nm_rec, uu____73008, uu____73042))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_73080 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_73080.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_73080.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_73080.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_73080.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_73080.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_73082 = env  in
                       let uu____73083 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_73085 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_73085.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_73085.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73083;
                         subst = (uu___1820_73082.subst);
                         tc_const = (uu___1820_73082.tc_const)
                       }  in
                     let uu____73086 = ensure_m env1 e21  in
                     (match uu____73086 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____73110 =
                              let uu____73111 =
                                let uu____73128 =
                                  let uu____73139 =
                                    let uu____73148 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____73151 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____73148, uu____73151)  in
                                  [uu____73139]  in
                                (s_e2, uu____73128)  in
                              FStar_Syntax_Syntax.Tm_app uu____73111  in
                            mk1 uu____73110  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____73193 =
                              let uu____73194 =
                                let uu____73211 =
                                  let uu____73222 =
                                    let uu____73231 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____73231)  in
                                  [uu____73222]  in
                                (s_e1, uu____73211)  in
                              FStar_Syntax_Syntax.Tm_app uu____73194  in
                            mk1 uu____73193  in
                          let uu____73267 =
                            let uu____73268 =
                              let uu____73269 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____73269]  in
                            FStar_Syntax_Util.abs uu____73268 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____73288 =
                            let uu____73289 =
                              let uu____73290 =
                                let uu____73304 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_73321 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_73321.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_73321.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_73321.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_73321.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_73321.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_73321.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73304)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73290  in
                            mk1 uu____73289  in
                          ((M t2), uu____73267, uu____73288)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73331 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____73331  in
      let uu____73332 = check env e mn  in
      match uu____73332 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73348 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____73371 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____73371  in
      let uu____73372 = check env e mn  in
      match uu____73372 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____73388 -> failwith "[check_m]: impossible"

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
        (let uu____73421 =
           let uu____73423 = is_C c  in Prims.op_Negation uu____73423  in
         if uu____73421 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____73437 =
           let uu____73438 = FStar_Syntax_Subst.compress c  in
           uu____73438.FStar_Syntax_Syntax.n  in
         match uu____73437 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____73467 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____73467 with
              | (wp_head,wp_args) ->
                  ((let uu____73511 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____73530 =
                           let uu____73532 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____73532
                            in
                         Prims.op_Negation uu____73530)
                       in
                    if uu____73511 then failwith "mismatch" else ());
                   (let uu____73545 =
                      let uu____73546 =
                        let uu____73563 =
                          FStar_List.map2
                            (fun uu____73601  ->
                               fun uu____73602  ->
                                 match (uu____73601, uu____73602) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____73664 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____73664
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____73673 =
                                         let uu____73675 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____73675 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____73673
                                       then
                                         let uu____73677 =
                                           let uu____73683 =
                                             let uu____73685 =
                                               print_implicit q  in
                                             let uu____73687 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____73685 uu____73687
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____73683)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____73677
                                       else ());
                                      (let uu____73693 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____73693, q)))) args wp_args
                           in
                        (head1, uu____73563)  in
                      FStar_Syntax_Syntax.Tm_app uu____73546  in
                    mk1 uu____73545)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____73739 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____73739 with
              | (binders_orig,comp1) ->
                  let uu____73746 =
                    let uu____73763 =
                      FStar_List.map
                        (fun uu____73803  ->
                           match uu____73803 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____73831 = is_C h  in
                               if uu____73831
                               then
                                 let w' =
                                   let uu____73847 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____73847
                                    in
                                 let uu____73849 =
                                   let uu____73858 =
                                     let uu____73867 =
                                       let uu____73874 =
                                         let uu____73875 =
                                           let uu____73876 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____73876  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____73875
                                          in
                                       (uu____73874, q)  in
                                     [uu____73867]  in
                                   (w', q) :: uu____73858  in
                                 (w', uu____73849)
                               else
                                 (let x =
                                    let uu____73910 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____73910
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____73763  in
                  (match uu____73746 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____73984 =
                           let uu____73987 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____73987
                            in
                         FStar_Syntax_Subst.subst_comp uu____73984 comp1  in
                       let app =
                         let uu____73991 =
                           let uu____73992 =
                             let uu____74009 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____74028 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____74029 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____74028, uu____74029)) bvs
                                in
                             (wp, uu____74009)  in
                           FStar_Syntax_Syntax.Tm_app uu____73992  in
                         mk1 uu____73991  in
                       let comp3 =
                         let uu____74044 = type_of_comp comp2  in
                         let uu____74045 = is_monadic_comp comp2  in
                         trans_G env uu____74044 uu____74045 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____74048,uu____74049) ->
             trans_F_ env e wp
         | uu____74090 -> failwith "impossible trans_F_")

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
            let uu____74098 =
              let uu____74099 = star_type' env h  in
              let uu____74102 =
                let uu____74113 =
                  let uu____74122 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____74122)  in
                [uu____74113]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____74099;
                FStar_Syntax_Syntax.effect_args = uu____74102;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____74098
          else
            (let uu____74148 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____74148)

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
    fun t  -> let uu____74169 = n env.tcenv t  in star_type' env uu____74169
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____74189 = n env.tcenv t  in check_n env uu____74189
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____74206 = n env.tcenv c  in
        let uu____74207 = n env.tcenv wp  in
        trans_F_ env uu____74206 uu____74207
  