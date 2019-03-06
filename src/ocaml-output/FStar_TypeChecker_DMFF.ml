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
              let uu___613_61778 = a  in
              let uu____61779 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_61778.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_61778.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____61779
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____61792 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____61792
             then
               (d "Elaborating extra WP combinators";
                (let uu____61798 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____61798))
             else ());
            (let rec collect_binders t =
               let uu____61817 =
                 let uu____61818 =
                   let uu____61821 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____61821
                    in
                 uu____61818.FStar_Syntax_Syntax.n  in
               match uu____61817 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____61856) -> t1
                     | uu____61865 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____61867 = collect_binders rest  in
                   FStar_List.append bs uu____61867
               | FStar_Syntax_Syntax.Tm_type uu____61882 -> []
               | uu____61889 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____61916 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____61916
                 FStar_Syntax_Util.name_binders
                in
             (let uu____61942 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____61942
              then
                let uu____61946 =
                  let uu____61948 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____61948  in
                d uu____61946
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____61986 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____61986 with
                | (sigelt,fv) ->
                    ((let uu____61994 =
                        let uu____61997 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____61997
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____61994);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____62077  ->
                     match uu____62077 with
                     | (t,b) ->
                         let uu____62091 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____62091))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____62130 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____62130))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____62164 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____62164)
                 in
              let uu____62167 =
                let uu____62184 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____62209 =
                        let uu____62212 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____62212  in
                      FStar_Syntax_Util.arrow gamma uu____62209  in
                    let uu____62213 =
                      let uu____62214 =
                        let uu____62223 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____62230 =
                          let uu____62239 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____62239]  in
                        uu____62223 :: uu____62230  in
                      FStar_List.append binders uu____62214  in
                    FStar_Syntax_Util.abs uu____62213 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____62270 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____62271 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____62270, uu____62271)  in
                match uu____62184 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____62313 =
                        let uu____62314 =
                          let uu____62331 =
                            let uu____62342 =
                              FStar_List.map
                                (fun uu____62364  ->
                                   match uu____62364 with
                                   | (bv,uu____62376) ->
                                       let uu____62381 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____62382 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____62381, uu____62382)) binders
                               in
                            let uu____62384 =
                              let uu____62391 =
                                let uu____62396 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____62397 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____62396, uu____62397)  in
                              let uu____62399 =
                                let uu____62406 =
                                  let uu____62411 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____62411)  in
                                [uu____62406]  in
                              uu____62391 :: uu____62399  in
                            FStar_List.append uu____62342 uu____62384  in
                          (fv, uu____62331)  in
                        FStar_Syntax_Syntax.Tm_app uu____62314  in
                      mk1 uu____62313  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____62167 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____62484 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____62484
                       in
                    let ret1 =
                      let uu____62489 =
                        let uu____62490 =
                          let uu____62493 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____62493  in
                        FStar_Syntax_Util.residual_tot uu____62490  in
                      FStar_Pervasives_Native.Some uu____62489  in
                    let body =
                      let uu____62497 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____62497 ret1  in
                    let uu____62500 =
                      let uu____62501 = mk_all_implicit binders  in
                      let uu____62508 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____62501 uu____62508  in
                    FStar_Syntax_Util.abs uu____62500 body ret1  in
                  let c_pure1 =
                    let uu____62546 = mk_lid "pure"  in
                    register env1 uu____62546 c_pure  in
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
                      let uu____62556 =
                        let uu____62557 =
                          let uu____62558 =
                            let uu____62567 =
                              let uu____62574 =
                                let uu____62575 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____62575
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____62574  in
                            [uu____62567]  in
                          let uu____62588 =
                            let uu____62591 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____62591  in
                          FStar_Syntax_Util.arrow uu____62558 uu____62588  in
                        mk_gctx uu____62557  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____62556
                       in
                    let r =
                      let uu____62594 =
                        let uu____62595 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62595  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____62594
                       in
                    let ret1 =
                      let uu____62600 =
                        let uu____62601 =
                          let uu____62604 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62604  in
                        FStar_Syntax_Util.residual_tot uu____62601  in
                      FStar_Pervasives_Native.Some uu____62600  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____62614 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____62617 =
                          let uu____62628 =
                            let uu____62631 =
                              let uu____62632 =
                                let uu____62633 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____62633
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____62632  in
                            [uu____62631]  in
                          FStar_List.append gamma_as_args uu____62628  in
                        FStar_Syntax_Util.mk_app uu____62614 uu____62617  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____62636 =
                      let uu____62637 = mk_all_implicit binders  in
                      let uu____62644 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____62637 uu____62644  in
                    FStar_Syntax_Util.abs uu____62636 outer_body ret1  in
                  let c_app1 =
                    let uu____62696 = mk_lid "app"  in
                    register env1 uu____62696 c_app  in
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
                      let uu____62708 =
                        let uu____62717 =
                          let uu____62724 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62724  in
                        [uu____62717]  in
                      let uu____62737 =
                        let uu____62740 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62740  in
                      FStar_Syntax_Util.arrow uu____62708 uu____62737  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62744 =
                        let uu____62745 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62745  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62744
                       in
                    let ret1 =
                      let uu____62750 =
                        let uu____62751 =
                          let uu____62754 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____62754  in
                        FStar_Syntax_Util.residual_tot uu____62751  in
                      FStar_Pervasives_Native.Some uu____62750  in
                    let uu____62755 =
                      let uu____62756 = mk_all_implicit binders  in
                      let uu____62763 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____62756 uu____62763  in
                    let uu____62814 =
                      let uu____62817 =
                        let uu____62828 =
                          let uu____62831 =
                            let uu____62832 =
                              let uu____62843 =
                                let uu____62846 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____62846]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____62843
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____62832  in
                          let uu____62855 =
                            let uu____62858 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____62858]  in
                          uu____62831 :: uu____62855  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____62828
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____62817  in
                    FStar_Syntax_Util.abs uu____62755 uu____62814 ret1  in
                  let c_lift11 =
                    let uu____62868 = mk_lid "lift1"  in
                    register env1 uu____62868 c_lift1  in
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
                      let uu____62882 =
                        let uu____62891 =
                          let uu____62898 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____62898  in
                        let uu____62899 =
                          let uu____62908 =
                            let uu____62915 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____62915  in
                          [uu____62908]  in
                        uu____62891 :: uu____62899  in
                      let uu____62934 =
                        let uu____62937 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____62937  in
                      FStar_Syntax_Util.arrow uu____62882 uu____62934  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____62941 =
                        let uu____62942 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____62942  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____62941
                       in
                    let a2 =
                      let uu____62945 =
                        let uu____62946 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____62946  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____62945
                       in
                    let ret1 =
                      let uu____62951 =
                        let uu____62952 =
                          let uu____62955 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____62955  in
                        FStar_Syntax_Util.residual_tot uu____62952  in
                      FStar_Pervasives_Native.Some uu____62951  in
                    let uu____62956 =
                      let uu____62957 = mk_all_implicit binders  in
                      let uu____62964 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____62957 uu____62964  in
                    let uu____63029 =
                      let uu____63032 =
                        let uu____63043 =
                          let uu____63046 =
                            let uu____63047 =
                              let uu____63058 =
                                let uu____63061 =
                                  let uu____63062 =
                                    let uu____63073 =
                                      let uu____63076 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____63076]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____63073
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____63062
                                   in
                                let uu____63085 =
                                  let uu____63088 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____63088]  in
                                uu____63061 :: uu____63085  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____63058
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____63047  in
                          let uu____63097 =
                            let uu____63100 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____63100]  in
                          uu____63046 :: uu____63097  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63043
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63032  in
                    FStar_Syntax_Util.abs uu____62956 uu____63029 ret1  in
                  let c_lift21 =
                    let uu____63110 = mk_lid "lift2"  in
                    register env1 uu____63110 c_lift2  in
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
                      let uu____63122 =
                        let uu____63131 =
                          let uu____63138 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____63138  in
                        [uu____63131]  in
                      let uu____63151 =
                        let uu____63154 =
                          let uu____63155 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____63155  in
                        FStar_Syntax_Syntax.mk_Total uu____63154  in
                      FStar_Syntax_Util.arrow uu____63122 uu____63151  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____63161 =
                        let uu____63162 =
                          let uu____63165 =
                            let uu____63166 =
                              let uu____63175 =
                                let uu____63182 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____63182
                                 in
                              [uu____63175]  in
                            let uu____63195 =
                              let uu____63198 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____63198  in
                            FStar_Syntax_Util.arrow uu____63166 uu____63195
                             in
                          mk_ctx uu____63165  in
                        FStar_Syntax_Util.residual_tot uu____63162  in
                      FStar_Pervasives_Native.Some uu____63161  in
                    let e1 =
                      let uu____63200 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____63200
                       in
                    let body =
                      let uu____63205 =
                        let uu____63206 =
                          let uu____63215 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____63215]  in
                        FStar_List.append gamma uu____63206  in
                      let uu____63240 =
                        let uu____63243 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____63246 =
                          let uu____63257 =
                            let uu____63258 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____63258  in
                          let uu____63259 = args_of_binders1 gamma  in
                          uu____63257 :: uu____63259  in
                        FStar_Syntax_Util.mk_app uu____63243 uu____63246  in
                      FStar_Syntax_Util.abs uu____63205 uu____63240 ret1  in
                    let uu____63262 =
                      let uu____63263 = mk_all_implicit binders  in
                      let uu____63270 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____63263 uu____63270  in
                    FStar_Syntax_Util.abs uu____63262 body ret1  in
                  let c_push1 =
                    let uu____63315 = mk_lid "push"  in
                    register env1 uu____63315 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____63342 =
                        let uu____63343 =
                          let uu____63360 = args_of_binders1 binders  in
                          (c, uu____63360)  in
                        FStar_Syntax_Syntax.Tm_app uu____63343  in
                      mk1 uu____63342
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____63389 =
                        let uu____63390 =
                          let uu____63399 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____63406 =
                            let uu____63415 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____63415]  in
                          uu____63399 :: uu____63406  in
                        let uu____63440 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____63390 uu____63440  in
                      FStar_Syntax_Syntax.mk_Total uu____63389  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____63445 =
                      let uu____63446 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____63446  in
                    let uu____63461 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____63466 =
                        let uu____63469 =
                          let uu____63480 =
                            let uu____63483 =
                              let uu____63484 =
                                let uu____63495 =
                                  let uu____63504 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____63504  in
                                [uu____63495]  in
                              FStar_Syntax_Util.mk_app l_ite uu____63484  in
                            [uu____63483]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____63480
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____63469  in
                      FStar_Syntax_Util.ascribe uu____63466
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____63445 uu____63461
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____63548 = mk_lid "wp_if_then_else"  in
                    register env1 uu____63548 wp_if_then_else  in
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
                      let uu____63565 =
                        let uu____63576 =
                          let uu____63579 =
                            let uu____63580 =
                              let uu____63591 =
                                let uu____63594 =
                                  let uu____63595 =
                                    let uu____63606 =
                                      let uu____63615 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____63615
                                       in
                                    [uu____63606]  in
                                  FStar_Syntax_Util.mk_app l_and uu____63595
                                   in
                                [uu____63594]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____63591
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____63580  in
                          let uu____63640 =
                            let uu____63643 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____63643]  in
                          uu____63579 :: uu____63640  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63576
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63565  in
                    let uu____63652 =
                      let uu____63653 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____63653  in
                    FStar_Syntax_Util.abs uu____63652 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____63669 = mk_lid "wp_assert"  in
                    register env1 uu____63669 wp_assert  in
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
                      let uu____63686 =
                        let uu____63697 =
                          let uu____63700 =
                            let uu____63701 =
                              let uu____63712 =
                                let uu____63715 =
                                  let uu____63716 =
                                    let uu____63727 =
                                      let uu____63736 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____63736
                                       in
                                    [uu____63727]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____63716
                                   in
                                [uu____63715]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____63712
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____63701  in
                          let uu____63761 =
                            let uu____63764 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____63764]  in
                          uu____63700 :: uu____63761  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63697
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63686  in
                    let uu____63773 =
                      let uu____63774 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____63774  in
                    FStar_Syntax_Util.abs uu____63773 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____63790 = mk_lid "wp_assume"  in
                    register env1 uu____63790 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____63803 =
                        let uu____63812 =
                          let uu____63819 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____63819  in
                        [uu____63812]  in
                      let uu____63832 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____63803 uu____63832  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____63840 =
                        let uu____63851 =
                          let uu____63854 =
                            let uu____63855 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____63855  in
                          let uu____63874 =
                            let uu____63877 =
                              let uu____63878 =
                                let uu____63889 =
                                  let uu____63892 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____63892]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____63889
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____63878
                               in
                            [uu____63877]  in
                          uu____63854 :: uu____63874  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____63851
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____63840  in
                    let uu____63909 =
                      let uu____63910 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____63910  in
                    FStar_Syntax_Util.abs uu____63909 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____63926 = mk_lid "wp_close"  in
                    register env1 uu____63926 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____63937 =
                      let uu____63938 =
                        let uu____63939 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____63939
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____63938
                       in
                    FStar_Pervasives_Native.Some uu____63937  in
                  let mk_forall1 x body =
                    let uu____63951 =
                      let uu____63958 =
                        let uu____63959 =
                          let uu____63976 =
                            let uu____63987 =
                              let uu____63996 =
                                let uu____63997 =
                                  let uu____63998 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____63998]  in
                                FStar_Syntax_Util.abs uu____63997 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____63996  in
                            [uu____63987]  in
                          (FStar_Syntax_Util.tforall, uu____63976)  in
                        FStar_Syntax_Syntax.Tm_app uu____63959  in
                      FStar_Syntax_Syntax.mk uu____63958  in
                    uu____63951 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____64056 =
                      let uu____64057 = FStar_Syntax_Subst.compress t  in
                      uu____64057.FStar_Syntax_Syntax.n  in
                    match uu____64056 with
                    | FStar_Syntax_Syntax.Tm_type uu____64061 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____64094  ->
                              match uu____64094 with
                              | (b,uu____64103) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____64108 -> true  in
                  let rec is_monotonic t =
                    let uu____64121 =
                      let uu____64122 = FStar_Syntax_Subst.compress t  in
                      uu____64122.FStar_Syntax_Syntax.n  in
                    match uu____64121 with
                    | FStar_Syntax_Syntax.Tm_type uu____64126 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____64159  ->
                              match uu____64159 with
                              | (b,uu____64168) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____64173 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____64247 =
                      let uu____64248 = FStar_Syntax_Subst.compress t1  in
                      uu____64248.FStar_Syntax_Syntax.n  in
                    match uu____64247 with
                    | FStar_Syntax_Syntax.Tm_type uu____64253 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____64256);
                                      FStar_Syntax_Syntax.pos = uu____64257;
                                      FStar_Syntax_Syntax.vars = uu____64258;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____64302 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____64302
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____64312 =
                              let uu____64315 =
                                let uu____64326 =
                                  let uu____64335 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____64335  in
                                [uu____64326]  in
                              FStar_Syntax_Util.mk_app x uu____64315  in
                            let uu____64352 =
                              let uu____64355 =
                                let uu____64366 =
                                  let uu____64375 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____64375  in
                                [uu____64366]  in
                              FStar_Syntax_Util.mk_app y uu____64355  in
                            mk_rel1 b uu____64312 uu____64352  in
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
                             let uu____64399 =
                               let uu____64402 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____64405 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____64402 uu____64405  in
                             let uu____64408 =
                               let uu____64411 =
                                 let uu____64414 =
                                   let uu____64425 =
                                     let uu____64434 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____64434
                                      in
                                   [uu____64425]  in
                                 FStar_Syntax_Util.mk_app x uu____64414  in
                               let uu____64451 =
                                 let uu____64454 =
                                   let uu____64465 =
                                     let uu____64474 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____64474
                                      in
                                   [uu____64465]  in
                                 FStar_Syntax_Util.mk_app y uu____64454  in
                               mk_rel1 b uu____64411 uu____64451  in
                             FStar_Syntax_Util.mk_imp uu____64399 uu____64408
                              in
                           let uu____64491 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____64491)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____64494);
                                      FStar_Syntax_Syntax.pos = uu____64495;
                                      FStar_Syntax_Syntax.vars = uu____64496;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____64540 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____64540
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____64550 =
                              let uu____64553 =
                                let uu____64564 =
                                  let uu____64573 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____64573  in
                                [uu____64564]  in
                              FStar_Syntax_Util.mk_app x uu____64553  in
                            let uu____64590 =
                              let uu____64593 =
                                let uu____64604 =
                                  let uu____64613 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____64613  in
                                [uu____64604]  in
                              FStar_Syntax_Util.mk_app y uu____64593  in
                            mk_rel1 b uu____64550 uu____64590  in
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
                             let uu____64637 =
                               let uu____64640 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____64643 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____64640 uu____64643  in
                             let uu____64646 =
                               let uu____64649 =
                                 let uu____64652 =
                                   let uu____64663 =
                                     let uu____64672 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____64672
                                      in
                                   [uu____64663]  in
                                 FStar_Syntax_Util.mk_app x uu____64652  in
                               let uu____64689 =
                                 let uu____64692 =
                                   let uu____64703 =
                                     let uu____64712 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____64712
                                      in
                                   [uu____64703]  in
                                 FStar_Syntax_Util.mk_app y uu____64692  in
                               mk_rel1 b uu____64649 uu____64689  in
                             FStar_Syntax_Util.mk_imp uu____64637 uu____64646
                              in
                           let uu____64729 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____64729)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_64768 = t1  in
                          let uu____64769 =
                            let uu____64770 =
                              let uu____64785 =
                                let uu____64788 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____64788  in
                              ([binder], uu____64785)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____64770  in
                          {
                            FStar_Syntax_Syntax.n = uu____64769;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_64768.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_64768.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____64811 ->
                        failwith "unhandled arrow"
                    | uu____64829 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____64866 =
                        let uu____64867 = FStar_Syntax_Subst.compress t1  in
                        uu____64867.FStar_Syntax_Syntax.n  in
                      match uu____64866 with
                      | FStar_Syntax_Syntax.Tm_type uu____64870 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____64897 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____64897
                          ->
                          let project i tuple =
                            let projector =
                              let uu____64918 =
                                let uu____64919 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____64919 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____64918
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____64949 =
                            let uu____64960 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____64978  ->
                                     match uu____64978 with
                                     | (t2,q) ->
                                         let uu____64998 = project i x  in
                                         let uu____65001 = project i y  in
                                         mk_stronger t2 uu____64998
                                           uu____65001) args
                               in
                            match uu____64960 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____64949 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____65055);
                                      FStar_Syntax_Syntax.pos = uu____65056;
                                      FStar_Syntax_Syntax.vars = uu____65057;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____65101  ->
                                   match uu____65101 with
                                   | (bv,q) ->
                                       let uu____65115 =
                                         let uu____65117 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____65117  in
                                       FStar_Syntax_Syntax.gen_bv uu____65115
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____65126 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____65126) bvs
                             in
                          let body =
                            let uu____65128 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____65131 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____65128 uu____65131  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____65140);
                                      FStar_Syntax_Syntax.pos = uu____65141;
                                      FStar_Syntax_Syntax.vars = uu____65142;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____65186  ->
                                   match uu____65186 with
                                   | (bv,q) ->
                                       let uu____65200 =
                                         let uu____65202 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____65202  in
                                       FStar_Syntax_Syntax.gen_bv uu____65200
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____65211 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____65211) bvs
                             in
                          let body =
                            let uu____65213 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____65216 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____65213 uu____65216  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____65223 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____65226 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____65229 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____65232 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____65226 uu____65229 uu____65232  in
                    let uu____65235 =
                      let uu____65236 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____65236  in
                    FStar_Syntax_Util.abs uu____65235 body ret_tot_type  in
                  let stronger1 =
                    let uu____65278 = mk_lid "stronger"  in
                    register env1 uu____65278 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____65286 = FStar_Util.prefix gamma  in
                    match uu____65286 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____65352 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____65352
                             in
                          let uu____65357 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____65357 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____65367 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____65367  in
                              let guard_free1 =
                                let uu____65379 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____65379  in
                              let pat =
                                let uu____65383 =
                                  let uu____65394 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____65394]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____65383
                                 in
                              let pattern_guarded_body =
                                let uu____65422 =
                                  let uu____65423 =
                                    let uu____65430 =
                                      let uu____65431 =
                                        let uu____65444 =
                                          let uu____65455 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____65455]  in
                                        [uu____65444]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____65431
                                       in
                                    (body, uu____65430)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____65423  in
                                mk1 uu____65422  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____65502 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____65511 =
                            let uu____65514 =
                              let uu____65515 =
                                let uu____65518 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____65521 =
                                  let uu____65532 = args_of_binders1 wp_args
                                     in
                                  let uu____65535 =
                                    let uu____65538 =
                                      let uu____65539 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____65539
                                       in
                                    [uu____65538]  in
                                  FStar_List.append uu____65532 uu____65535
                                   in
                                FStar_Syntax_Util.mk_app uu____65518
                                  uu____65521
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____65515  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____65514
                             in
                          FStar_Syntax_Util.abs gamma uu____65511
                            ret_gtot_type
                           in
                        let uu____65540 =
                          let uu____65541 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____65541  in
                        FStar_Syntax_Util.abs uu____65540 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____65557 = mk_lid "ite_wp"  in
                    register env1 uu____65557 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____65565 = FStar_Util.prefix gamma  in
                    match uu____65565 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____65623 =
                            let uu____65624 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____65631 =
                              let uu____65642 =
                                let uu____65651 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____65651  in
                              [uu____65642]  in
                            FStar_Syntax_Util.mk_app uu____65624 uu____65631
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____65623
                           in
                        let uu____65668 =
                          let uu____65669 =
                            let uu____65678 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____65678 gamma  in
                          FStar_List.append binders uu____65669  in
                        FStar_Syntax_Util.abs uu____65668 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____65700 = mk_lid "null_wp"  in
                    register env1 uu____65700 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____65713 =
                        let uu____65724 =
                          let uu____65727 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____65728 =
                            let uu____65731 =
                              let uu____65732 =
                                let uu____65743 =
                                  let uu____65752 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____65752  in
                                [uu____65743]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____65732
                               in
                            let uu____65769 =
                              let uu____65772 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____65772]  in
                            uu____65731 :: uu____65769  in
                          uu____65727 :: uu____65728  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____65724
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____65713  in
                    let uu____65781 =
                      let uu____65782 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____65782  in
                    FStar_Syntax_Util.abs uu____65781 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____65798 = mk_lid "wp_trivial"  in
                    register env1 uu____65798 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____65804 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____65804
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____65816 =
                      let uu____65817 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____65817  in
                    let uu____65843 =
                      let uu___934_65844 = ed  in
                      let uu____65845 =
                        let uu____65846 = c wp_if_then_else2  in
                        ([], uu____65846)  in
                      let uu____65853 =
                        let uu____65854 = c ite_wp2  in ([], uu____65854)  in
                      let uu____65861 =
                        let uu____65862 = c stronger2  in ([], uu____65862)
                         in
                      let uu____65869 =
                        let uu____65870 = c wp_close2  in ([], uu____65870)
                         in
                      let uu____65877 =
                        let uu____65878 = c wp_assert2  in ([], uu____65878)
                         in
                      let uu____65885 =
                        let uu____65886 = c wp_assume2  in ([], uu____65886)
                         in
                      let uu____65893 =
                        let uu____65894 = c null_wp2  in ([], uu____65894)
                         in
                      let uu____65901 =
                        let uu____65902 = c wp_trivial2  in ([], uu____65902)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_65844.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_65844.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_65844.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_65844.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_65844.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_65844.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_65844.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____65845;
                        FStar_Syntax_Syntax.ite_wp = uu____65853;
                        FStar_Syntax_Syntax.stronger = uu____65861;
                        FStar_Syntax_Syntax.close_wp = uu____65869;
                        FStar_Syntax_Syntax.assert_p = uu____65877;
                        FStar_Syntax_Syntax.assume_p = uu____65885;
                        FStar_Syntax_Syntax.null_wp = uu____65893;
                        FStar_Syntax_Syntax.trivial = uu____65901;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_65844.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_65844.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_65844.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_65844.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_65844.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____65816, uu____65843)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_65926 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_65926.subst);
        tc_const = (uu___939_65926.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____65947 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____65967 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____65988) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_66002  ->
                match uu___585_66002 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____66005 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____66007 ->
        let uu____66008 =
          let uu____66014 =
            let uu____66016 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____66016
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____66014)  in
        FStar_Errors.raise_error uu____66008 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_66026  ->
    match uu___586_66026 with
    | N t ->
        let uu____66029 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____66029
    | M t ->
        let uu____66033 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____66033
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____66042,c) -> nm_of_comp c
    | uu____66064 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____66077 = nm_of_comp c  in
    match uu____66077 with | M uu____66079 -> true | N uu____66081 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____66092 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____66108 =
        let uu____66117 =
          let uu____66124 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____66124  in
        [uu____66117]  in
      let uu____66143 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____66108 uu____66143  in
    let uu____66146 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____66146
  
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
        let uu____66188 =
          let uu____66189 =
            let uu____66204 =
              let uu____66213 =
                let uu____66220 =
                  let uu____66221 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____66221  in
                let uu____66222 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____66220, uu____66222)  in
              [uu____66213]  in
            let uu____66240 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____66204, uu____66240)  in
          FStar_Syntax_Syntax.Tm_arrow uu____66189  in
        mk1 uu____66188

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____66280) ->
          let binders1 =
            FStar_List.map
              (fun uu____66326  ->
                 match uu____66326 with
                 | (bv,aqual) ->
                     let uu____66345 =
                       let uu___989_66346 = bv  in
                       let uu____66347 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_66346.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_66346.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____66347
                       }  in
                     (uu____66345, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____66352,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____66354);
                              FStar_Syntax_Syntax.pos = uu____66355;
                              FStar_Syntax_Syntax.vars = uu____66356;_})
               ->
               let uu____66385 =
                 let uu____66386 =
                   let uu____66401 =
                     let uu____66404 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____66404  in
                   (binders1, uu____66401)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____66386  in
               mk1 uu____66385
           | uu____66415 ->
               let uu____66416 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____66416 with
                | N hn ->
                    let uu____66418 =
                      let uu____66419 =
                        let uu____66434 =
                          let uu____66437 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____66437  in
                        (binders1, uu____66434)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____66419  in
                    mk1 uu____66418
                | M a ->
                    let uu____66449 =
                      let uu____66450 =
                        let uu____66465 =
                          let uu____66474 =
                            let uu____66483 =
                              let uu____66490 =
                                let uu____66491 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____66491  in
                              let uu____66492 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____66490, uu____66492)  in
                            [uu____66483]  in
                          FStar_List.append binders1 uu____66474  in
                        let uu____66516 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____66465, uu____66516)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____66450  in
                    mk1 uu____66449))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____66610 = f x  in
                    FStar_Util.string_builder_append strb uu____66610);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____66619 = f x1  in
                         FStar_Util.string_builder_append strb uu____66619))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____66623 =
              let uu____66629 =
                let uu____66631 = FStar_Syntax_Print.term_to_string t2  in
                let uu____66633 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____66631 uu____66633
                 in
              (FStar_Errors.Warning_DependencyFound, uu____66629)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____66623  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____66655 =
              let uu____66656 = FStar_Syntax_Subst.compress ty  in
              uu____66656.FStar_Syntax_Syntax.n  in
            match uu____66655 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____66682 =
                  let uu____66684 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____66684  in
                if uu____66682
                then false
                else
                  (try
                     (fun uu___1038_66701  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____66725 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____66725 s  in
                              let uu____66728 =
                                let uu____66730 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____66730  in
                              if uu____66728
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____66736 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____66736 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____66761  ->
                                          match uu____66761 with
                                          | (bv,uu____66773) ->
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
            | uu____66801 ->
                ((let uu____66803 =
                    let uu____66809 =
                      let uu____66811 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____66811
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____66809)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____66803);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____66827 =
              let uu____66828 = FStar_Syntax_Subst.compress head2  in
              uu____66828.FStar_Syntax_Syntax.n  in
            match uu____66827 with
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
                  (let uu____66834 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____66834)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____66837 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____66837 with
                 | ((uu____66847,ty),uu____66849) ->
                     let uu____66854 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____66854
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____66867 =
                         let uu____66868 = FStar_Syntax_Subst.compress res
                            in
                         uu____66868.FStar_Syntax_Syntax.n  in
                       (match uu____66867 with
                        | FStar_Syntax_Syntax.Tm_app uu____66872 -> true
                        | uu____66890 ->
                            ((let uu____66892 =
                                let uu____66898 =
                                  let uu____66900 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____66900
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____66898)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____66892);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____66908 -> true
            | FStar_Syntax_Syntax.Tm_name uu____66910 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____66913) ->
                is_valid_application t2
            | uu____66918 -> false  in
          let uu____66920 = is_valid_application head1  in
          if uu____66920
          then
            let uu____66923 =
              let uu____66924 =
                let uu____66941 =
                  FStar_List.map
                    (fun uu____66970  ->
                       match uu____66970 with
                       | (t2,qual) ->
                           let uu____66995 = star_type' env t2  in
                           (uu____66995, qual)) args
                   in
                (head1, uu____66941)  in
              FStar_Syntax_Syntax.Tm_app uu____66924  in
            mk1 uu____66923
          else
            (let uu____67012 =
               let uu____67018 =
                 let uu____67020 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____67020
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____67018)  in
             FStar_Errors.raise_err uu____67012)
      | FStar_Syntax_Syntax.Tm_bvar uu____67024 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____67025 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____67026 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____67027 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____67055 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____67055 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_67063 = env  in
                 let uu____67064 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____67064;
                   subst = (uu___1110_67063.subst);
                   tc_const = (uu___1110_67063.tc_const)
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
               ((let uu___1125_67091 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_67091.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_67091.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____67098 =
            let uu____67099 =
              let uu____67106 = star_type' env t2  in (uu____67106, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____67099  in
          mk1 uu____67098
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____67158 =
            let uu____67159 =
              let uu____67186 = star_type' env e  in
              let uu____67189 =
                let uu____67206 =
                  let uu____67215 = star_type' env t2  in
                  FStar_Util.Inl uu____67215  in
                (uu____67206, FStar_Pervasives_Native.None)  in
              (uu____67186, uu____67189, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____67159  in
          mk1 uu____67158
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____67303 =
            let uu____67304 =
              let uu____67331 = star_type' env e  in
              let uu____67334 =
                let uu____67351 =
                  let uu____67360 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____67360  in
                (uu____67351, FStar_Pervasives_Native.None)  in
              (uu____67331, uu____67334, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____67304  in
          mk1 uu____67303
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____67401,(uu____67402,FStar_Pervasives_Native.Some uu____67403),uu____67404)
          ->
          let uu____67453 =
            let uu____67459 =
              let uu____67461 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____67461
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67459)  in
          FStar_Errors.raise_err uu____67453
      | FStar_Syntax_Syntax.Tm_refine uu____67465 ->
          let uu____67472 =
            let uu____67478 =
              let uu____67480 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____67480
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67478)  in
          FStar_Errors.raise_err uu____67472
      | FStar_Syntax_Syntax.Tm_uinst uu____67484 ->
          let uu____67491 =
            let uu____67497 =
              let uu____67499 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____67499
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67497)  in
          FStar_Errors.raise_err uu____67491
      | FStar_Syntax_Syntax.Tm_quoted uu____67503 ->
          let uu____67510 =
            let uu____67516 =
              let uu____67518 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____67518
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67516)  in
          FStar_Errors.raise_err uu____67510
      | FStar_Syntax_Syntax.Tm_constant uu____67522 ->
          let uu____67523 =
            let uu____67529 =
              let uu____67531 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____67531
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67529)  in
          FStar_Errors.raise_err uu____67523
      | FStar_Syntax_Syntax.Tm_match uu____67535 ->
          let uu____67558 =
            let uu____67564 =
              let uu____67566 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____67566
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67564)  in
          FStar_Errors.raise_err uu____67558
      | FStar_Syntax_Syntax.Tm_let uu____67570 ->
          let uu____67584 =
            let uu____67590 =
              let uu____67592 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____67592
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67590)  in
          FStar_Errors.raise_err uu____67584
      | FStar_Syntax_Syntax.Tm_uvar uu____67596 ->
          let uu____67609 =
            let uu____67615 =
              let uu____67617 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____67617
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67615)  in
          FStar_Errors.raise_err uu____67609
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____67621 =
            let uu____67627 =
              let uu____67629 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____67629
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____67627)  in
          FStar_Errors.raise_err uu____67621
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____67634 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____67634
      | FStar_Syntax_Syntax.Tm_delayed uu____67637 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_67669  ->
    match uu___588_67669 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_67680  ->
                match uu___587_67680 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____67683 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____67693 =
      let uu____67694 = FStar_Syntax_Subst.compress t  in
      uu____67694.FStar_Syntax_Syntax.n  in
    match uu____67693 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____67726 =
            let uu____67727 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____67727  in
          is_C uu____67726  in
        if r
        then
          ((let uu____67751 =
              let uu____67753 =
                FStar_List.for_all
                  (fun uu____67764  ->
                     match uu____67764 with | (h,uu____67773) -> is_C h) args
                 in
              Prims.op_Negation uu____67753  in
            if uu____67751 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____67786 =
              let uu____67788 =
                FStar_List.for_all
                  (fun uu____67800  ->
                     match uu____67800 with
                     | (h,uu____67809) ->
                         let uu____67814 = is_C h  in
                         Prims.op_Negation uu____67814) args
                 in
              Prims.op_Negation uu____67788  in
            if uu____67786 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____67843 = nm_of_comp comp  in
        (match uu____67843 with
         | M t1 ->
             ((let uu____67847 = is_C t1  in
               if uu____67847 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____67856) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____67862) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____67868,uu____67869) -> is_C t1
    | uu____67910 -> false
  
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
          let uu____67946 =
            let uu____67947 =
              let uu____67964 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____67967 =
                let uu____67978 =
                  let uu____67987 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____67987)  in
                [uu____67978]  in
              (uu____67964, uu____67967)  in
            FStar_Syntax_Syntax.Tm_app uu____67947  in
          mk1 uu____67946  in
        let uu____68023 =
          let uu____68024 = FStar_Syntax_Syntax.mk_binder p  in [uu____68024]
           in
        FStar_Syntax_Util.abs uu____68023 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_68049  ->
    match uu___589_68049 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____68052 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____68290 =
          match uu____68290 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____68327 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____68330 =
                       let uu____68332 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____68332  in
                     Prims.op_Negation uu____68330)
                   in
                if uu____68327
                then
                  let uu____68334 =
                    let uu____68340 =
                      let uu____68342 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____68344 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____68346 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____68342 uu____68344 uu____68346
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____68340)  in
                  FStar_Errors.raise_err uu____68334
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____68371 = mk_return env t1 s_e  in
                     ((M t1), uu____68371, u_e)))
               | (M t1,N t2) ->
                   let uu____68378 =
                     let uu____68384 =
                       let uu____68386 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____68388 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____68390 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____68386 uu____68388 uu____68390
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____68384)
                      in
                   FStar_Errors.raise_err uu____68378)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_68442 =
            match uu___590_68442 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____68458 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____68479 =
                let uu____68485 =
                  let uu____68487 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____68487
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____68485)  in
              FStar_Errors.raise_error uu____68479 e2.FStar_Syntax_Syntax.pos
          | M uu____68497 ->
              let uu____68498 = check env1 e2 context_nm  in
              strip_m uu____68498
           in
        let uu____68505 =
          let uu____68506 = FStar_Syntax_Subst.compress e  in
          uu____68506.FStar_Syntax_Syntax.n  in
        match uu____68505 with
        | FStar_Syntax_Syntax.Tm_bvar uu____68515 ->
            let uu____68516 = infer env e  in return_if uu____68516
        | FStar_Syntax_Syntax.Tm_name uu____68523 ->
            let uu____68524 = infer env e  in return_if uu____68524
        | FStar_Syntax_Syntax.Tm_fvar uu____68531 ->
            let uu____68532 = infer env e  in return_if uu____68532
        | FStar_Syntax_Syntax.Tm_abs uu____68539 ->
            let uu____68558 = infer env e  in return_if uu____68558
        | FStar_Syntax_Syntax.Tm_constant uu____68565 ->
            let uu____68566 = infer env e  in return_if uu____68566
        | FStar_Syntax_Syntax.Tm_quoted uu____68573 ->
            let uu____68580 = infer env e  in return_if uu____68580
        | FStar_Syntax_Syntax.Tm_app uu____68587 ->
            let uu____68604 = infer env e  in return_if uu____68604
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____68612 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____68612 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____68677) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____68683) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____68689,uu____68690) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____68731 ->
            let uu____68745 =
              let uu____68747 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____68747  in
            failwith uu____68745
        | FStar_Syntax_Syntax.Tm_type uu____68756 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____68764 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____68786 ->
            let uu____68793 =
              let uu____68795 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____68795  in
            failwith uu____68793
        | FStar_Syntax_Syntax.Tm_uvar uu____68804 ->
            let uu____68817 =
              let uu____68819 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____68819  in
            failwith uu____68817
        | FStar_Syntax_Syntax.Tm_delayed uu____68828 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____68858 =
              let uu____68860 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____68860  in
            failwith uu____68858

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
      let uu____68890 =
        let uu____68891 = FStar_Syntax_Subst.compress e  in
        uu____68891.FStar_Syntax_Syntax.n  in
      match uu____68890 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____68910 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____68910
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____68961;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____68962;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____68968 =
                  let uu___1360_68969 = rc  in
                  let uu____68970 =
                    let uu____68975 =
                      let uu____68978 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____68978  in
                    FStar_Pervasives_Native.Some uu____68975  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_68969.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____68970;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_68969.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____68968
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_68990 = env  in
            let uu____68991 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____68991;
              subst = (uu___1366_68990.subst);
              tc_const = (uu___1366_68990.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____69017  ->
                 match uu____69017 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_69040 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_69040.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_69040.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____69041 =
            FStar_List.fold_left
              (fun uu____69072  ->
                 fun uu____69073  ->
                   match (uu____69072, uu____69073) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____69131 = is_C c  in
                       if uu____69131
                       then
                         let xw =
                           let uu____69141 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____69141
                            in
                         let x =
                           let uu___1385_69144 = bv  in
                           let uu____69145 =
                             let uu____69148 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____69148  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_69144.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_69144.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____69145
                           }  in
                         let env3 =
                           let uu___1388_69150 = env2  in
                           let uu____69151 =
                             let uu____69154 =
                               let uu____69155 =
                                 let uu____69162 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____69162)  in
                               FStar_Syntax_Syntax.NT uu____69155  in
                             uu____69154 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_69150.tcenv);
                             subst = uu____69151;
                             tc_const = (uu___1388_69150.tc_const)
                           }  in
                         let uu____69167 =
                           let uu____69170 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____69171 =
                             let uu____69174 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____69174 :: acc  in
                           uu____69170 :: uu____69171  in
                         (env3, uu____69167)
                       else
                         (let x =
                            let uu___1391_69180 = bv  in
                            let uu____69181 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_69180.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_69180.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____69181
                            }  in
                          let uu____69184 =
                            let uu____69187 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____69187 :: acc  in
                          (env2, uu____69184))) (env1, []) binders1
             in
          (match uu____69041 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____69207 =
                 let check_what =
                   let uu____69233 = is_monadic rc_opt1  in
                   if uu____69233 then check_m else check_n  in
                 let uu____69250 = check_what env2 body1  in
                 match uu____69250 with
                 | (t,s_body,u_body) ->
                     let uu____69270 =
                       let uu____69273 =
                         let uu____69274 = is_monadic rc_opt1  in
                         if uu____69274 then M t else N t  in
                       comp_of_nm uu____69273  in
                     (uu____69270, s_body, u_body)
                  in
               (match uu____69207 with
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
                                 let uu____69314 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_69320  ->
                                           match uu___591_69320 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____69323 -> false))
                                    in
                                 if uu____69314
                                 then
                                   let uu____69326 =
                                     FStar_List.filter
                                       (fun uu___592_69330  ->
                                          match uu___592_69330 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____69333 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____69326
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____69344 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_69350  ->
                                         match uu___593_69350 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____69353 -> false))
                                  in
                               if uu____69344
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_69362  ->
                                        match uu___594_69362 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____69365 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____69367 =
                                   let uu____69368 =
                                     let uu____69373 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____69373
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____69368 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____69367
                               else
                                 (let uu____69380 =
                                    let uu___1432_69381 = rc  in
                                    let uu____69382 =
                                      let uu____69387 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____69387
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_69381.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____69382;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_69381.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____69380))
                       in
                    let uu____69392 =
                      let comp1 =
                        let uu____69400 = is_monadic rc_opt1  in
                        let uu____69402 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____69400 uu____69402
                         in
                      let uu____69403 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____69403,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____69392 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____69441 =
                             let uu____69442 =
                               let uu____69461 =
                                 let uu____69464 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____69464 s_rc_opt  in
                               (s_binders1, s_body1, uu____69461)  in
                             FStar_Syntax_Syntax.Tm_abs uu____69442  in
                           mk1 uu____69441  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____69484 =
                             let uu____69485 =
                               let uu____69504 =
                                 let uu____69507 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____69507 u_rc_opt  in
                               (u_binders2, u_body2, uu____69504)  in
                             FStar_Syntax_Syntax.Tm_abs uu____69485  in
                           mk1 uu____69484  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____69523;_};
            FStar_Syntax_Syntax.fv_delta = uu____69524;
            FStar_Syntax_Syntax.fv_qual = uu____69525;_}
          ->
          let uu____69528 =
            let uu____69533 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____69533  in
          (match uu____69528 with
           | (uu____69564,t) ->
               let uu____69566 =
                 let uu____69567 = normalize1 t  in N uu____69567  in
               (uu____69566, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69568;
             FStar_Syntax_Syntax.vars = uu____69569;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____69648 = FStar_Syntax_Util.head_and_args e  in
          (match uu____69648 with
           | (unary_op1,uu____69672) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____69743;
             FStar_Syntax_Syntax.vars = uu____69744;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____69840 = FStar_Syntax_Util.head_and_args e  in
          (match uu____69840 with
           | (unary_op1,uu____69864) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____69943;
             FStar_Syntax_Syntax.vars = uu____69944;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____69982 = infer env a  in
          (match uu____69982 with
           | (t,s,u) ->
               let uu____69998 = FStar_Syntax_Util.head_and_args e  in
               (match uu____69998 with
                | (head1,uu____70022) ->
                    let uu____70047 =
                      let uu____70048 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____70048  in
                    let uu____70049 =
                      let uu____70050 =
                        let uu____70051 =
                          let uu____70068 =
                            let uu____70079 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____70079]  in
                          (head1, uu____70068)  in
                        FStar_Syntax_Syntax.Tm_app uu____70051  in
                      mk1 uu____70050  in
                    let uu____70116 =
                      let uu____70117 =
                        let uu____70118 =
                          let uu____70135 =
                            let uu____70146 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____70146]  in
                          (head1, uu____70135)  in
                        FStar_Syntax_Syntax.Tm_app uu____70118  in
                      mk1 uu____70117  in
                    (uu____70047, uu____70049, uu____70116)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____70183;
             FStar_Syntax_Syntax.vars = uu____70184;_},(a1,uu____70186)::a2::[])
          ->
          let uu____70242 = infer env a1  in
          (match uu____70242 with
           | (t,s,u) ->
               let uu____70258 = FStar_Syntax_Util.head_and_args e  in
               (match uu____70258 with
                | (head1,uu____70282) ->
                    let uu____70307 =
                      let uu____70308 =
                        let uu____70309 =
                          let uu____70326 =
                            let uu____70337 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____70337; a2]  in
                          (head1, uu____70326)  in
                        FStar_Syntax_Syntax.Tm_app uu____70309  in
                      mk1 uu____70308  in
                    let uu____70382 =
                      let uu____70383 =
                        let uu____70384 =
                          let uu____70401 =
                            let uu____70412 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____70412; a2]  in
                          (head1, uu____70401)  in
                        FStar_Syntax_Syntax.Tm_app uu____70384  in
                      mk1 uu____70383  in
                    (t, uu____70307, uu____70382)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____70457;
             FStar_Syntax_Syntax.vars = uu____70458;_},uu____70459)
          ->
          let uu____70484 =
            let uu____70490 =
              let uu____70492 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____70492
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____70490)  in
          FStar_Errors.raise_error uu____70484 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____70502;
             FStar_Syntax_Syntax.vars = uu____70503;_},uu____70504)
          ->
          let uu____70529 =
            let uu____70535 =
              let uu____70537 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____70537
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____70535)  in
          FStar_Errors.raise_error uu____70529 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____70573 = check_n env head1  in
          (match uu____70573 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____70596 =
                   let uu____70597 = FStar_Syntax_Subst.compress t  in
                   uu____70597.FStar_Syntax_Syntax.n  in
                 match uu____70596 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____70601 -> true
                 | uu____70617 -> false  in
               let rec flatten1 t =
                 let uu____70639 =
                   let uu____70640 = FStar_Syntax_Subst.compress t  in
                   uu____70640.FStar_Syntax_Syntax.n  in
                 match uu____70639 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____70659);
                                FStar_Syntax_Syntax.pos = uu____70660;
                                FStar_Syntax_Syntax.vars = uu____70661;_})
                     when is_arrow t1 ->
                     let uu____70690 = flatten1 t1  in
                     (match uu____70690 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____70790,uu____70791) -> flatten1 e1
                 | uu____70832 ->
                     let uu____70833 =
                       let uu____70839 =
                         let uu____70841 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____70841
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____70839)  in
                     FStar_Errors.raise_err uu____70833
                  in
               let uu____70859 = flatten1 t_head  in
               (match uu____70859 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____70934 =
                          let uu____70940 =
                            let uu____70942 = FStar_Util.string_of_int n1  in
                            let uu____70944 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____70946 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____70942 uu____70944 uu____70946
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____70940)
                           in
                        FStar_Errors.raise_err uu____70934)
                     else ();
                     (let uu____70952 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____70952 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____71005 args1 =
                            match uu____71005 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____71105 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____71105
                                 | (binders3,[]) ->
                                     let uu____71143 =
                                       let uu____71144 =
                                         let uu____71147 =
                                           let uu____71148 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____71148
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____71147
                                          in
                                       uu____71144.FStar_Syntax_Syntax.n  in
                                     (match uu____71143 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____71181 =
                                            let uu____71182 =
                                              let uu____71183 =
                                                let uu____71198 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____71198)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____71183
                                               in
                                            mk1 uu____71182  in
                                          N uu____71181
                                      | uu____71211 -> failwith "wat?")
                                 | ([],uu____71213::uu____71214) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____71267)::binders3,(arg,uu____71270)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____71357 = FStar_List.splitAt n' binders1
                             in
                          (match uu____71357 with
                           | (binders2,uu____71391) ->
                               let uu____71424 =
                                 let uu____71447 =
                                   FStar_List.map2
                                     (fun uu____71509  ->
                                        fun uu____71510  ->
                                          match (uu____71509, uu____71510)
                                          with
                                          | ((bv,uu____71558),(arg,q)) ->
                                              let uu____71587 =
                                                let uu____71588 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____71588.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____71587 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____71609 ->
                                                   let uu____71610 =
                                                     let uu____71617 =
                                                       star_type' env arg  in
                                                     (uu____71617, q)  in
                                                   (uu____71610, [(arg, q)])
                                               | uu____71654 ->
                                                   let uu____71655 =
                                                     check_n env arg  in
                                                   (match uu____71655 with
                                                    | (uu____71680,s_arg,u_arg)
                                                        ->
                                                        let uu____71683 =
                                                          let uu____71692 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____71692
                                                          then
                                                            let uu____71703 =
                                                              let uu____71710
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____71710,
                                                                q)
                                                               in
                                                            [uu____71703;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____71683))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____71447  in
                               (match uu____71424 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____71838 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____71851 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____71838, uu____71851)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____71920) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____71926) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____71932,uu____71933) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____71975 =
            let uu____71976 = env.tc_const c  in N uu____71976  in
          (uu____71975, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____71983 ->
          let uu____71997 =
            let uu____71999 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____71999  in
          failwith uu____71997
      | FStar_Syntax_Syntax.Tm_type uu____72008 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____72016 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____72038 ->
          let uu____72045 =
            let uu____72047 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____72047  in
          failwith uu____72045
      | FStar_Syntax_Syntax.Tm_uvar uu____72056 ->
          let uu____72069 =
            let uu____72071 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____72071  in
          failwith uu____72069
      | FStar_Syntax_Syntax.Tm_delayed uu____72080 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____72110 =
            let uu____72112 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____72112  in
          failwith uu____72110

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
          let uu____72161 = check_n env e0  in
          match uu____72161 with
          | (uu____72174,s_e0,u_e0) ->
              let uu____72177 =
                let uu____72206 =
                  FStar_List.map
                    (fun b  ->
                       let uu____72267 = FStar_Syntax_Subst.open_branch b  in
                       match uu____72267 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_72309 = env  in
                             let uu____72310 =
                               let uu____72311 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____72311
                                in
                             {
                               tcenv = uu____72310;
                               subst = (uu___1707_72309.subst);
                               tc_const = (uu___1707_72309.tc_const)
                             }  in
                           let uu____72314 = f env1 body  in
                           (match uu____72314 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____72386 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____72206  in
              (match uu____72177 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____72492 = FStar_List.hd nms  in
                     match uu____72492 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_72501  ->
                          match uu___595_72501 with
                          | M uu____72503 -> true
                          | uu____72505 -> false) nms
                      in
                   let uu____72507 =
                     let uu____72544 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____72634  ->
                              match uu____72634 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____72818 =
                                         check env original_body (M t2)  in
                                       (match uu____72818 with
                                        | (uu____72855,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____72894,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____72544  in
                   (match uu____72507 with
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
                              (fun uu____73083  ->
                                 match uu____73083 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____73134 =
                                         let uu____73135 =
                                           let uu____73152 =
                                             let uu____73163 =
                                               let uu____73172 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____73175 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____73172, uu____73175)  in
                                             [uu____73163]  in
                                           (s_body, uu____73152)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____73135
                                          in
                                       mk1 uu____73134  in
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
                            let uu____73310 =
                              let uu____73311 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____73311]  in
                            let uu____73330 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____73310 uu____73330
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____73354 =
                              let uu____73363 =
                                let uu____73370 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____73370
                                 in
                              [uu____73363]  in
                            let uu____73389 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____73354 uu____73389
                             in
                          let uu____73392 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____73431 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____73392, uu____73431)
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
                           let uu____73541 =
                             let uu____73542 =
                               let uu____73543 =
                                 let uu____73570 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____73570,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____73543
                                in
                             mk1 uu____73542  in
                           let uu____73629 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____73541, uu____73629))))

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
              let uu____73694 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____73694]  in
            let uu____73713 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____73713 with
            | (x_binders1,e21) ->
                let uu____73726 = infer env e1  in
                (match uu____73726 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____73743 = is_C t1  in
                       if uu____73743
                       then
                         let uu___1793_73746 = binding  in
                         let uu____73747 =
                           let uu____73750 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____73750  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_73746.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_73746.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____73747;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_73746.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_73746.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_73746.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_73746.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_73754 = env  in
                       let uu____73755 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_73757 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_73757.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_73757.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73755;
                         subst = (uu___1796_73754.subst);
                         tc_const = (uu___1796_73754.tc_const)
                       }  in
                     let uu____73758 = proceed env1 e21  in
                     (match uu____73758 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_73775 = binding  in
                            let uu____73776 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_73775.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_73775.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____73776;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_73775.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_73775.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_73775.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_73775.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____73779 =
                            let uu____73780 =
                              let uu____73781 =
                                let uu____73795 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_73812 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_73812.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_73812.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_73812.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_73812.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_73812.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_73812.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73795)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73781  in
                            mk1 uu____73780  in
                          let uu____73813 =
                            let uu____73814 =
                              let uu____73815 =
                                let uu____73829 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_73846 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_73846.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_73846.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_73846.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_73846.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_73846.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_73846.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____73829)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____73815  in
                            mk1 uu____73814  in
                          (nm_rec, uu____73779, uu____73813))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_73851 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_73851.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_73851.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_73851.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_73851.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_73851.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_73853 = env  in
                       let uu____73854 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_73856 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_73856.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_73856.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____73854;
                         subst = (uu___1820_73853.subst);
                         tc_const = (uu___1820_73853.tc_const)
                       }  in
                     let uu____73857 = ensure_m env1 e21  in
                     (match uu____73857 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____73881 =
                              let uu____73882 =
                                let uu____73899 =
                                  let uu____73910 =
                                    let uu____73919 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____73922 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____73919, uu____73922)  in
                                  [uu____73910]  in
                                (s_e2, uu____73899)  in
                              FStar_Syntax_Syntax.Tm_app uu____73882  in
                            mk1 uu____73881  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____73964 =
                              let uu____73965 =
                                let uu____73982 =
                                  let uu____73993 =
                                    let uu____74002 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____74002)  in
                                  [uu____73993]  in
                                (s_e1, uu____73982)  in
                              FStar_Syntax_Syntax.Tm_app uu____73965  in
                            mk1 uu____73964  in
                          let uu____74038 =
                            let uu____74039 =
                              let uu____74040 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____74040]  in
                            FStar_Syntax_Util.abs uu____74039 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____74059 =
                            let uu____74060 =
                              let uu____74061 =
                                let uu____74075 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_74092 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_74092.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_74092.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_74092.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_74092.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_74092.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_74092.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____74075)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____74061  in
                            mk1 uu____74060  in
                          ((M t2), uu____74038, uu____74059)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____74102 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____74102  in
      let uu____74103 = check env e mn  in
      match uu____74103 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____74119 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____74142 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____74142  in
      let uu____74143 = check env e mn  in
      match uu____74143 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____74159 -> failwith "[check_m]: impossible"

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
        (let uu____74192 =
           let uu____74194 = is_C c  in Prims.op_Negation uu____74194  in
         if uu____74192 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____74208 =
           let uu____74209 = FStar_Syntax_Subst.compress c  in
           uu____74209.FStar_Syntax_Syntax.n  in
         match uu____74208 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____74238 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____74238 with
              | (wp_head,wp_args) ->
                  ((let uu____74282 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____74301 =
                           let uu____74303 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____74303
                            in
                         Prims.op_Negation uu____74301)
                       in
                    if uu____74282 then failwith "mismatch" else ());
                   (let uu____74316 =
                      let uu____74317 =
                        let uu____74334 =
                          FStar_List.map2
                            (fun uu____74372  ->
                               fun uu____74373  ->
                                 match (uu____74372, uu____74373) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____74435 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____74435
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____74444 =
                                         let uu____74446 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____74446 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____74444
                                       then
                                         let uu____74448 =
                                           let uu____74454 =
                                             let uu____74456 =
                                               print_implicit q  in
                                             let uu____74458 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____74456 uu____74458
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____74454)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____74448
                                       else ());
                                      (let uu____74464 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____74464, q)))) args wp_args
                           in
                        (head1, uu____74334)  in
                      FStar_Syntax_Syntax.Tm_app uu____74317  in
                    mk1 uu____74316)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____74510 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____74510 with
              | (binders_orig,comp1) ->
                  let uu____74517 =
                    let uu____74534 =
                      FStar_List.map
                        (fun uu____74574  ->
                           match uu____74574 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____74602 = is_C h  in
                               if uu____74602
                               then
                                 let w' =
                                   let uu____74618 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____74618
                                    in
                                 let uu____74620 =
                                   let uu____74629 =
                                     let uu____74638 =
                                       let uu____74645 =
                                         let uu____74646 =
                                           let uu____74647 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____74647  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____74646
                                          in
                                       (uu____74645, q)  in
                                     [uu____74638]  in
                                   (w', q) :: uu____74629  in
                                 (w', uu____74620)
                               else
                                 (let x =
                                    let uu____74681 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____74681
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____74534  in
                  (match uu____74517 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____74755 =
                           let uu____74758 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____74758
                            in
                         FStar_Syntax_Subst.subst_comp uu____74755 comp1  in
                       let app =
                         let uu____74762 =
                           let uu____74763 =
                             let uu____74780 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____74799 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____74800 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____74799, uu____74800)) bvs
                                in
                             (wp, uu____74780)  in
                           FStar_Syntax_Syntax.Tm_app uu____74763  in
                         mk1 uu____74762  in
                       let comp3 =
                         let uu____74815 = type_of_comp comp2  in
                         let uu____74816 = is_monadic_comp comp2  in
                         trans_G env uu____74815 uu____74816 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____74819,uu____74820) ->
             trans_F_ env e wp
         | uu____74861 -> failwith "impossible trans_F_")

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
            let uu____74869 =
              let uu____74870 = star_type' env h  in
              let uu____74873 =
                let uu____74884 =
                  let uu____74893 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____74893)  in
                [uu____74884]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____74870;
                FStar_Syntax_Syntax.effect_args = uu____74873;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____74869
          else
            (let uu____74919 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____74919)

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
    fun t  -> let uu____74940 = n env.tcenv t  in star_type' env uu____74940
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____74960 = n env.tcenv t  in check_n env uu____74960
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____74977 = n env.tcenv c  in
        let uu____74978 = n env.tcenv wp  in
        trans_F_ env uu____74977 uu____74978
  