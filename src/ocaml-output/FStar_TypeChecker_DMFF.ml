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
              let uu___613_65893 = a  in
              let uu____65894 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_65893.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_65893.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____65894
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____65907 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____65907
             then
               (d "Elaborating extra WP combinators";
                (let uu____65913 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____65913))
             else ());
            (let rec collect_binders t =
               let uu____65932 =
                 let uu____65933 =
                   let uu____65936 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____65936
                    in
                 uu____65933.FStar_Syntax_Syntax.n  in
               match uu____65932 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____65971) -> t1
                     | uu____65980 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____65982 = collect_binders rest  in
                   FStar_List.append bs uu____65982
               | FStar_Syntax_Syntax.Tm_type uu____65997 -> []
               | uu____66004 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____66031 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____66031
                 FStar_Syntax_Util.name_binders
                in
             (let uu____66057 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____66057
              then
                let uu____66061 =
                  let uu____66063 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____66063  in
                d uu____66061
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____66101 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____66101 with
                | (sigelt,fv) ->
                    ((let uu____66109 =
                        let uu____66112 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____66112
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____66109);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____66236  ->
                     match uu____66236 with
                     | (t,b) ->
                         let uu____66250 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____66250))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____66289 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____66289))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____66323 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____66323)
                 in
              let uu____66326 =
                let uu____66343 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____66368 =
                        let uu____66371 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____66371  in
                      FStar_Syntax_Util.arrow gamma uu____66368  in
                    let uu____66372 =
                      let uu____66373 =
                        let uu____66382 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____66389 =
                          let uu____66398 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____66398]  in
                        uu____66382 :: uu____66389  in
                      FStar_List.append binders uu____66373  in
                    FStar_Syntax_Util.abs uu____66372 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____66429 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____66430 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____66429, uu____66430)  in
                match uu____66343 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____66472 =
                        let uu____66473 =
                          let uu____66490 =
                            let uu____66501 =
                              FStar_List.map
                                (fun uu____66523  ->
                                   match uu____66523 with
                                   | (bv,uu____66535) ->
                                       let uu____66540 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____66541 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____66540, uu____66541)) binders
                               in
                            let uu____66543 =
                              let uu____66550 =
                                let uu____66555 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____66556 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____66555, uu____66556)  in
                              let uu____66558 =
                                let uu____66565 =
                                  let uu____66570 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____66570)  in
                                [uu____66565]  in
                              uu____66550 :: uu____66558  in
                            FStar_List.append uu____66501 uu____66543  in
                          (fv, uu____66490)  in
                        FStar_Syntax_Syntax.Tm_app uu____66473  in
                      mk1 uu____66472  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____66326 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____66643 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____66643
                       in
                    let ret1 =
                      let uu____66648 =
                        let uu____66649 =
                          let uu____66652 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____66652  in
                        FStar_Syntax_Util.residual_tot uu____66649  in
                      FStar_Pervasives_Native.Some uu____66648  in
                    let body =
                      let uu____66656 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____66656 ret1  in
                    let uu____66659 =
                      let uu____66660 = mk_all_implicit binders  in
                      let uu____66667 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____66660 uu____66667  in
                    FStar_Syntax_Util.abs uu____66659 body ret1  in
                  let c_pure1 =
                    let uu____66705 = mk_lid "pure"  in
                    register env1 uu____66705 c_pure  in
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
                      let uu____66715 =
                        let uu____66716 =
                          let uu____66717 =
                            let uu____66726 =
                              let uu____66733 =
                                let uu____66734 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____66734
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____66733  in
                            [uu____66726]  in
                          let uu____66747 =
                            let uu____66750 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____66750  in
                          FStar_Syntax_Util.arrow uu____66717 uu____66747  in
                        mk_gctx uu____66716  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____66715
                       in
                    let r =
                      let uu____66753 =
                        let uu____66754 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66754  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____66753
                       in
                    let ret1 =
                      let uu____66759 =
                        let uu____66760 =
                          let uu____66763 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66763  in
                        FStar_Syntax_Util.residual_tot uu____66760  in
                      FStar_Pervasives_Native.Some uu____66759  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____66773 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____66776 =
                          let uu____66787 =
                            let uu____66790 =
                              let uu____66791 =
                                let uu____66792 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____66792
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____66791  in
                            [uu____66790]  in
                          FStar_List.append gamma_as_args uu____66787  in
                        FStar_Syntax_Util.mk_app uu____66773 uu____66776  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____66795 =
                      let uu____66796 = mk_all_implicit binders  in
                      let uu____66803 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____66796 uu____66803  in
                    FStar_Syntax_Util.abs uu____66795 outer_body ret1  in
                  let c_app1 =
                    let uu____66855 = mk_lid "app"  in
                    register env1 uu____66855 c_app  in
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
                      let uu____66867 =
                        let uu____66876 =
                          let uu____66883 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____66883  in
                        [uu____66876]  in
                      let uu____66896 =
                        let uu____66899 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____66899  in
                      FStar_Syntax_Util.arrow uu____66867 uu____66896  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____66903 =
                        let uu____66904 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66904  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____66903
                       in
                    let ret1 =
                      let uu____66909 =
                        let uu____66910 =
                          let uu____66913 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66913  in
                        FStar_Syntax_Util.residual_tot uu____66910  in
                      FStar_Pervasives_Native.Some uu____66909  in
                    let uu____66914 =
                      let uu____66915 = mk_all_implicit binders  in
                      let uu____66922 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____66915 uu____66922  in
                    let uu____66973 =
                      let uu____66976 =
                        let uu____66987 =
                          let uu____66990 =
                            let uu____66991 =
                              let uu____67002 =
                                let uu____67005 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____67005]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67002
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____66991  in
                          let uu____67014 =
                            let uu____67017 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____67017]  in
                          uu____66990 :: uu____67014  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____66987
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____66976  in
                    FStar_Syntax_Util.abs uu____66914 uu____66973 ret1  in
                  let c_lift11 =
                    let uu____67027 = mk_lid "lift1"  in
                    register env1 uu____67027 c_lift1  in
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
                      let uu____67041 =
                        let uu____67050 =
                          let uu____67057 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67057  in
                        let uu____67058 =
                          let uu____67067 =
                            let uu____67074 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____67074  in
                          [uu____67067]  in
                        uu____67050 :: uu____67058  in
                      let uu____67093 =
                        let uu____67096 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____67096  in
                      FStar_Syntax_Util.arrow uu____67041 uu____67093  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____67100 =
                        let uu____67101 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____67101  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____67100
                       in
                    let a2 =
                      let uu____67104 =
                        let uu____67105 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____67105  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____67104
                       in
                    let ret1 =
                      let uu____67110 =
                        let uu____67111 =
                          let uu____67114 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____67114  in
                        FStar_Syntax_Util.residual_tot uu____67111  in
                      FStar_Pervasives_Native.Some uu____67110  in
                    let uu____67115 =
                      let uu____67116 = mk_all_implicit binders  in
                      let uu____67123 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____67116 uu____67123  in
                    let uu____67188 =
                      let uu____67191 =
                        let uu____67202 =
                          let uu____67205 =
                            let uu____67206 =
                              let uu____67217 =
                                let uu____67220 =
                                  let uu____67221 =
                                    let uu____67232 =
                                      let uu____67235 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____67235]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____67232
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____67221
                                   in
                                let uu____67244 =
                                  let uu____67247 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____67247]  in
                                uu____67220 :: uu____67244  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67217
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____67206  in
                          let uu____67256 =
                            let uu____67259 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____67259]  in
                          uu____67205 :: uu____67256  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67202
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67191  in
                    FStar_Syntax_Util.abs uu____67115 uu____67188 ret1  in
                  let c_lift21 =
                    let uu____67269 = mk_lid "lift2"  in
                    register env1 uu____67269 c_lift2  in
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
                      let uu____67281 =
                        let uu____67290 =
                          let uu____67297 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67297  in
                        [uu____67290]  in
                      let uu____67310 =
                        let uu____67313 =
                          let uu____67314 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____67314  in
                        FStar_Syntax_Syntax.mk_Total uu____67313  in
                      FStar_Syntax_Util.arrow uu____67281 uu____67310  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____67320 =
                        let uu____67321 =
                          let uu____67324 =
                            let uu____67325 =
                              let uu____67334 =
                                let uu____67341 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____67341
                                 in
                              [uu____67334]  in
                            let uu____67354 =
                              let uu____67357 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____67357  in
                            FStar_Syntax_Util.arrow uu____67325 uu____67354
                             in
                          mk_ctx uu____67324  in
                        FStar_Syntax_Util.residual_tot uu____67321  in
                      FStar_Pervasives_Native.Some uu____67320  in
                    let e1 =
                      let uu____67359 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____67359
                       in
                    let body =
                      let uu____67364 =
                        let uu____67365 =
                          let uu____67374 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____67374]  in
                        FStar_List.append gamma uu____67365  in
                      let uu____67399 =
                        let uu____67402 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____67405 =
                          let uu____67416 =
                            let uu____67417 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____67417  in
                          let uu____67418 = args_of_binders1 gamma  in
                          uu____67416 :: uu____67418  in
                        FStar_Syntax_Util.mk_app uu____67402 uu____67405  in
                      FStar_Syntax_Util.abs uu____67364 uu____67399 ret1  in
                    let uu____67421 =
                      let uu____67422 = mk_all_implicit binders  in
                      let uu____67429 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____67422 uu____67429  in
                    FStar_Syntax_Util.abs uu____67421 body ret1  in
                  let c_push1 =
                    let uu____67474 = mk_lid "push"  in
                    register env1 uu____67474 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____67501 =
                        let uu____67502 =
                          let uu____67519 = args_of_binders1 binders  in
                          (c, uu____67519)  in
                        FStar_Syntax_Syntax.Tm_app uu____67502  in
                      mk1 uu____67501
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____67548 =
                        let uu____67549 =
                          let uu____67558 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____67565 =
                            let uu____67574 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____67574]  in
                          uu____67558 :: uu____67565  in
                        let uu____67599 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____67549 uu____67599  in
                      FStar_Syntax_Syntax.mk_Total uu____67548  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____67604 =
                      let uu____67605 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____67605  in
                    let uu____67620 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____67625 =
                        let uu____67628 =
                          let uu____67639 =
                            let uu____67642 =
                              let uu____67643 =
                                let uu____67654 =
                                  let uu____67663 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____67663  in
                                [uu____67654]  in
                              FStar_Syntax_Util.mk_app l_ite uu____67643  in
                            [uu____67642]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____67639
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____67628  in
                      FStar_Syntax_Util.ascribe uu____67625
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____67604 uu____67620
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____67707 = mk_lid "wp_if_then_else"  in
                    register env1 uu____67707 wp_if_then_else  in
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
                      let uu____67724 =
                        let uu____67735 =
                          let uu____67738 =
                            let uu____67739 =
                              let uu____67750 =
                                let uu____67753 =
                                  let uu____67754 =
                                    let uu____67765 =
                                      let uu____67774 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67774
                                       in
                                    [uu____67765]  in
                                  FStar_Syntax_Util.mk_app l_and uu____67754
                                   in
                                [uu____67753]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67750
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67739  in
                          let uu____67799 =
                            let uu____67802 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67802]  in
                          uu____67738 :: uu____67799  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67735
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67724  in
                    let uu____67811 =
                      let uu____67812 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67812  in
                    FStar_Syntax_Util.abs uu____67811 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____67828 = mk_lid "wp_assert"  in
                    register env1 uu____67828 wp_assert  in
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
                      let uu____67845 =
                        let uu____67856 =
                          let uu____67859 =
                            let uu____67860 =
                              let uu____67871 =
                                let uu____67874 =
                                  let uu____67875 =
                                    let uu____67886 =
                                      let uu____67895 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67895
                                       in
                                    [uu____67886]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____67875
                                   in
                                [uu____67874]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67871
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67860  in
                          let uu____67920 =
                            let uu____67923 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67923]  in
                          uu____67859 :: uu____67920  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67856
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67845  in
                    let uu____67932 =
                      let uu____67933 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67933  in
                    FStar_Syntax_Util.abs uu____67932 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____67949 = mk_lid "wp_assume"  in
                    register env1 uu____67949 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____67962 =
                        let uu____67971 =
                          let uu____67978 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____67978  in
                        [uu____67971]  in
                      let uu____67991 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____67962 uu____67991  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____67999 =
                        let uu____68010 =
                          let uu____68013 =
                            let uu____68014 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____68014  in
                          let uu____68033 =
                            let uu____68036 =
                              let uu____68037 =
                                let uu____68048 =
                                  let uu____68051 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____68051]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____68048
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____68037
                               in
                            [uu____68036]  in
                          uu____68013 :: uu____68033  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____68010
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67999  in
                    let uu____68068 =
                      let uu____68069 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____68069  in
                    FStar_Syntax_Util.abs uu____68068 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____68085 = mk_lid "wp_close"  in
                    register env1 uu____68085 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____68096 =
                      let uu____68097 =
                        let uu____68098 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____68098
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____68097
                       in
                    FStar_Pervasives_Native.Some uu____68096  in
                  let mk_forall1 x body =
                    let uu____68110 =
                      let uu____68117 =
                        let uu____68118 =
                          let uu____68135 =
                            let uu____68146 =
                              let uu____68155 =
                                let uu____68156 =
                                  let uu____68157 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____68157]  in
                                FStar_Syntax_Util.abs uu____68156 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____68155  in
                            [uu____68146]  in
                          (FStar_Syntax_Util.tforall, uu____68135)  in
                        FStar_Syntax_Syntax.Tm_app uu____68118  in
                      FStar_Syntax_Syntax.mk uu____68117  in
                    uu____68110 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____68218 =
                      let uu____68219 = FStar_Syntax_Subst.compress t  in
                      uu____68219.FStar_Syntax_Syntax.n  in
                    match uu____68218 with
                    | FStar_Syntax_Syntax.Tm_type uu____68223 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68256  ->
                              match uu____68256 with
                              | (b,uu____68265) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____68270 -> true  in
                  let rec is_monotonic t =
                    let uu____68283 =
                      let uu____68284 = FStar_Syntax_Subst.compress t  in
                      uu____68284.FStar_Syntax_Syntax.n  in
                    match uu____68283 with
                    | FStar_Syntax_Syntax.Tm_type uu____68288 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68321  ->
                              match uu____68321 with
                              | (b,uu____68330) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____68335 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____68409 =
                      let uu____68410 = FStar_Syntax_Subst.compress t1  in
                      uu____68410.FStar_Syntax_Syntax.n  in
                    match uu____68409 with
                    | FStar_Syntax_Syntax.Tm_type uu____68415 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____68418);
                                      FStar_Syntax_Syntax.pos = uu____68419;
                                      FStar_Syntax_Syntax.vars = uu____68420;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68464 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68464
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68474 =
                              let uu____68477 =
                                let uu____68488 =
                                  let uu____68497 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68497  in
                                [uu____68488]  in
                              FStar_Syntax_Util.mk_app x uu____68477  in
                            let uu____68514 =
                              let uu____68517 =
                                let uu____68528 =
                                  let uu____68537 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68537  in
                                [uu____68528]  in
                              FStar_Syntax_Util.mk_app y uu____68517  in
                            mk_rel1 b uu____68474 uu____68514  in
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
                             let uu____68561 =
                               let uu____68564 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68567 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68564 uu____68567  in
                             let uu____68570 =
                               let uu____68573 =
                                 let uu____68576 =
                                   let uu____68587 =
                                     let uu____68596 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68596
                                      in
                                   [uu____68587]  in
                                 FStar_Syntax_Util.mk_app x uu____68576  in
                               let uu____68613 =
                                 let uu____68616 =
                                   let uu____68627 =
                                     let uu____68636 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68636
                                      in
                                   [uu____68627]  in
                                 FStar_Syntax_Util.mk_app y uu____68616  in
                               mk_rel1 b uu____68573 uu____68613  in
                             FStar_Syntax_Util.mk_imp uu____68561 uu____68570
                              in
                           let uu____68653 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68653)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____68656);
                                      FStar_Syntax_Syntax.pos = uu____68657;
                                      FStar_Syntax_Syntax.vars = uu____68658;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68702 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68702
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68712 =
                              let uu____68715 =
                                let uu____68726 =
                                  let uu____68735 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68735  in
                                [uu____68726]  in
                              FStar_Syntax_Util.mk_app x uu____68715  in
                            let uu____68752 =
                              let uu____68755 =
                                let uu____68766 =
                                  let uu____68775 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68775  in
                                [uu____68766]  in
                              FStar_Syntax_Util.mk_app y uu____68755  in
                            mk_rel1 b uu____68712 uu____68752  in
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
                             let uu____68799 =
                               let uu____68802 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68805 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68802 uu____68805  in
                             let uu____68808 =
                               let uu____68811 =
                                 let uu____68814 =
                                   let uu____68825 =
                                     let uu____68834 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68834
                                      in
                                   [uu____68825]  in
                                 FStar_Syntax_Util.mk_app x uu____68814  in
                               let uu____68851 =
                                 let uu____68854 =
                                   let uu____68865 =
                                     let uu____68874 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68874
                                      in
                                   [uu____68865]  in
                                 FStar_Syntax_Util.mk_app y uu____68854  in
                               mk_rel1 b uu____68811 uu____68851  in
                             FStar_Syntax_Util.mk_imp uu____68799 uu____68808
                              in
                           let uu____68891 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68891)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_68930 = t1  in
                          let uu____68931 =
                            let uu____68932 =
                              let uu____68947 =
                                let uu____68950 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____68950  in
                              ([binder], uu____68947)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____68932  in
                          {
                            FStar_Syntax_Syntax.n = uu____68931;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_68930.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_68930.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____68973 ->
                        failwith "unhandled arrow"
                    | uu____68991 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____69028 =
                        let uu____69029 = FStar_Syntax_Subst.compress t1  in
                        uu____69029.FStar_Syntax_Syntax.n  in
                      match uu____69028 with
                      | FStar_Syntax_Syntax.Tm_type uu____69032 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____69059 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____69059
                          ->
                          let project i tuple =
                            let projector =
                              let uu____69080 =
                                let uu____69081 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____69081 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____69080
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____69111 =
                            let uu____69122 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____69140  ->
                                     match uu____69140 with
                                     | (t2,q) ->
                                         let uu____69160 = project i x  in
                                         let uu____69163 = project i y  in
                                         mk_stronger t2 uu____69160
                                           uu____69163) args
                               in
                            match uu____69122 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____69111 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____69217);
                                      FStar_Syntax_Syntax.pos = uu____69218;
                                      FStar_Syntax_Syntax.vars = uu____69219;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69263  ->
                                   match uu____69263 with
                                   | (bv,q) ->
                                       let uu____69277 =
                                         let uu____69279 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69279  in
                                       FStar_Syntax_Syntax.gen_bv uu____69277
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69288 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69288) bvs
                             in
                          let body =
                            let uu____69290 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69293 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69290 uu____69293  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____69302);
                                      FStar_Syntax_Syntax.pos = uu____69303;
                                      FStar_Syntax_Syntax.vars = uu____69304;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69348  ->
                                   match uu____69348 with
                                   | (bv,q) ->
                                       let uu____69362 =
                                         let uu____69364 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69364  in
                                       FStar_Syntax_Syntax.gen_bv uu____69362
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69373 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69373) bvs
                             in
                          let body =
                            let uu____69375 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69378 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69375 uu____69378  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____69385 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____69388 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____69391 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____69394 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____69388 uu____69391 uu____69394  in
                    let uu____69397 =
                      let uu____69398 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____69398  in
                    FStar_Syntax_Util.abs uu____69397 body ret_tot_type  in
                  let stronger1 =
                    let uu____69440 = mk_lid "stronger"  in
                    register env1 uu____69440 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69448 = FStar_Util.prefix gamma  in
                    match uu____69448 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____69514 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____69514
                             in
                          let uu____69519 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____69519 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____69529 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____69529  in
                              let guard_free1 =
                                let uu____69541 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____69541  in
                              let pat =
                                let uu____69545 =
                                  let uu____69556 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____69556]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____69545
                                 in
                              let pattern_guarded_body =
                                let uu____69584 =
                                  let uu____69585 =
                                    let uu____69592 =
                                      let uu____69593 =
                                        let uu____69606 =
                                          let uu____69617 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____69617]  in
                                        [uu____69606]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____69593
                                       in
                                    (body, uu____69592)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____69585  in
                                mk1 uu____69584  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____69664 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____69673 =
                            let uu____69676 =
                              let uu____69677 =
                                let uu____69680 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____69683 =
                                  let uu____69694 = args_of_binders1 wp_args
                                     in
                                  let uu____69697 =
                                    let uu____69700 =
                                      let uu____69701 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____69701
                                       in
                                    [uu____69700]  in
                                  FStar_List.append uu____69694 uu____69697
                                   in
                                FStar_Syntax_Util.mk_app uu____69680
                                  uu____69683
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____69677  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____69676
                             in
                          FStar_Syntax_Util.abs gamma uu____69673
                            ret_gtot_type
                           in
                        let uu____69702 =
                          let uu____69703 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____69703  in
                        FStar_Syntax_Util.abs uu____69702 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____69719 = mk_lid "ite_wp"  in
                    register env1 uu____69719 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69727 = FStar_Util.prefix gamma  in
                    match uu____69727 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____69785 =
                            let uu____69786 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____69793 =
                              let uu____69804 =
                                let uu____69813 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____69813  in
                              [uu____69804]  in
                            FStar_Syntax_Util.mk_app uu____69786 uu____69793
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____69785
                           in
                        let uu____69830 =
                          let uu____69831 =
                            let uu____69840 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____69840 gamma  in
                          FStar_List.append binders uu____69831  in
                        FStar_Syntax_Util.abs uu____69830 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____69862 = mk_lid "null_wp"  in
                    register env1 uu____69862 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____69875 =
                        let uu____69886 =
                          let uu____69889 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____69890 =
                            let uu____69893 =
                              let uu____69894 =
                                let uu____69905 =
                                  let uu____69914 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____69914  in
                                [uu____69905]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____69894
                               in
                            let uu____69931 =
                              let uu____69934 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____69934]  in
                            uu____69893 :: uu____69931  in
                          uu____69889 :: uu____69890  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____69886
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____69875  in
                    let uu____69943 =
                      let uu____69944 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____69944  in
                    FStar_Syntax_Util.abs uu____69943 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____69960 = mk_lid "wp_trivial"  in
                    register env1 uu____69960 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____69966 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____69966
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____69978 =
                      let uu____69979 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____69979  in
                    let uu____70027 =
                      let uu___934_70028 = ed  in
                      let uu____70029 =
                        let uu____70030 = c wp_if_then_else2  in
                        ([], uu____70030)  in
                      let uu____70037 =
                        let uu____70038 = c ite_wp2  in ([], uu____70038)  in
                      let uu____70045 =
                        let uu____70046 = c stronger2  in ([], uu____70046)
                         in
                      let uu____70053 =
                        let uu____70054 = c wp_close2  in ([], uu____70054)
                         in
                      let uu____70061 =
                        let uu____70062 = c wp_assert2  in ([], uu____70062)
                         in
                      let uu____70069 =
                        let uu____70070 = c wp_assume2  in ([], uu____70070)
                         in
                      let uu____70077 =
                        let uu____70078 = c null_wp2  in ([], uu____70078)
                         in
                      let uu____70085 =
                        let uu____70086 = c wp_trivial2  in ([], uu____70086)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_70028.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_70028.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_70028.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_70028.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_70028.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_70028.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_70028.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____70029;
                        FStar_Syntax_Syntax.ite_wp = uu____70037;
                        FStar_Syntax_Syntax.stronger = uu____70045;
                        FStar_Syntax_Syntax.close_wp = uu____70053;
                        FStar_Syntax_Syntax.assert_p = uu____70061;
                        FStar_Syntax_Syntax.assume_p = uu____70069;
                        FStar_Syntax_Syntax.null_wp = uu____70077;
                        FStar_Syntax_Syntax.trivial = uu____70085;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_70028.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_70028.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_70028.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_70028.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_70028.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____69978, uu____70027)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_70110 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_70110.subst);
        tc_const = (uu___939_70110.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____70131 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____70151 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____70172) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_70186  ->
                match uu___585_70186 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____70189 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____70191 ->
        let uu____70192 =
          let uu____70198 =
            let uu____70200 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____70200
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____70198)  in
        FStar_Errors.raise_error uu____70192 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_70210  ->
    match uu___586_70210 with
    | N t ->
        let uu____70213 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____70213
    | M t ->
        let uu____70217 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____70217
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____70226,c) -> nm_of_comp c
    | uu____70248 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____70261 = nm_of_comp c  in
    match uu____70261 with | M uu____70263 -> true | N uu____70265 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____70276 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____70292 =
        let uu____70301 =
          let uu____70308 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____70308  in
        [uu____70301]  in
      let uu____70327 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____70292 uu____70327  in
    let uu____70330 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____70330
  
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
        let uu____70372 =
          let uu____70373 =
            let uu____70388 =
              let uu____70397 =
                let uu____70404 =
                  let uu____70405 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____70405  in
                let uu____70406 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____70404, uu____70406)  in
              [uu____70397]  in
            let uu____70424 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____70388, uu____70424)  in
          FStar_Syntax_Syntax.Tm_arrow uu____70373  in
        mk1 uu____70372

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70464) ->
          let binders1 =
            FStar_List.map
              (fun uu____70510  ->
                 match uu____70510 with
                 | (bv,aqual) ->
                     let uu____70529 =
                       let uu___989_70530 = bv  in
                       let uu____70531 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_70530.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_70530.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____70531
                       }  in
                     (uu____70529, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____70536,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____70538);
                              FStar_Syntax_Syntax.pos = uu____70539;
                              FStar_Syntax_Syntax.vars = uu____70540;_})
               ->
               let uu____70569 =
                 let uu____70570 =
                   let uu____70585 =
                     let uu____70588 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____70588  in
                   (binders1, uu____70585)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____70570  in
               mk1 uu____70569
           | uu____70599 ->
               let uu____70600 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____70600 with
                | N hn ->
                    let uu____70602 =
                      let uu____70603 =
                        let uu____70618 =
                          let uu____70621 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____70621  in
                        (binders1, uu____70618)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70603  in
                    mk1 uu____70602
                | M a ->
                    let uu____70633 =
                      let uu____70634 =
                        let uu____70649 =
                          let uu____70658 =
                            let uu____70667 =
                              let uu____70674 =
                                let uu____70675 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____70675  in
                              let uu____70676 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____70674, uu____70676)  in
                            [uu____70667]  in
                          FStar_List.append binders1 uu____70658  in
                        let uu____70700 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____70649, uu____70700)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70634  in
                    mk1 uu____70633))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____70794 = f x  in
                    FStar_Util.string_builder_append strb uu____70794);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____70803 = f x1  in
                         FStar_Util.string_builder_append strb uu____70803))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____70807 =
              let uu____70813 =
                let uu____70815 = FStar_Syntax_Print.term_to_string t2  in
                let uu____70817 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____70815 uu____70817
                 in
              (FStar_Errors.Warning_DependencyFound, uu____70813)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____70807  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____70839 =
              let uu____70840 = FStar_Syntax_Subst.compress ty  in
              uu____70840.FStar_Syntax_Syntax.n  in
            match uu____70839 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____70866 =
                  let uu____70868 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____70868  in
                if uu____70866
                then false
                else
                  (try
                     (fun uu___1038_70885  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____70909 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____70909 s  in
                              let uu____70912 =
                                let uu____70914 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____70914  in
                              if uu____70912
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____70920 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____70920 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____70945  ->
                                          match uu____70945 with
                                          | (bv,uu____70957) ->
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
            | uu____70985 ->
                ((let uu____70987 =
                    let uu____70993 =
                      let uu____70995 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____70995
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____70993)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____70987);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____71011 =
              let uu____71012 = FStar_Syntax_Subst.compress head2  in
              uu____71012.FStar_Syntax_Syntax.n  in
            match uu____71011 with
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
                  (let uu____71018 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____71018)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____71021 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____71021 with
                 | ((uu____71031,ty),uu____71033) ->
                     let uu____71038 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____71038
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____71051 =
                         let uu____71052 = FStar_Syntax_Subst.compress res
                            in
                         uu____71052.FStar_Syntax_Syntax.n  in
                       (match uu____71051 with
                        | FStar_Syntax_Syntax.Tm_app uu____71056 -> true
                        | uu____71074 ->
                            ((let uu____71076 =
                                let uu____71082 =
                                  let uu____71084 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____71084
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____71082)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____71076);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____71092 -> true
            | FStar_Syntax_Syntax.Tm_name uu____71094 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71097) ->
                is_valid_application t2
            | uu____71102 -> false  in
          let uu____71104 = is_valid_application head1  in
          if uu____71104
          then
            let uu____71107 =
              let uu____71108 =
                let uu____71125 =
                  FStar_List.map
                    (fun uu____71154  ->
                       match uu____71154 with
                       | (t2,qual) ->
                           let uu____71179 = star_type' env t2  in
                           (uu____71179, qual)) args
                   in
                (head1, uu____71125)  in
              FStar_Syntax_Syntax.Tm_app uu____71108  in
            mk1 uu____71107
          else
            (let uu____71196 =
               let uu____71202 =
                 let uu____71204 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____71204
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____71202)  in
             FStar_Errors.raise_err uu____71196)
      | FStar_Syntax_Syntax.Tm_bvar uu____71208 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____71209 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____71210 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____71211 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____71239 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____71239 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_71247 = env  in
                 let uu____71248 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____71248;
                   subst = (uu___1110_71247.subst);
                   tc_const = (uu___1110_71247.tc_const)
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
               ((let uu___1125_71275 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_71275.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_71275.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____71282 =
            let uu____71283 =
              let uu____71290 = star_type' env t2  in (uu____71290, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____71283  in
          mk1 uu____71282
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____71342 =
            let uu____71343 =
              let uu____71370 = star_type' env e  in
              let uu____71373 =
                let uu____71390 =
                  let uu____71399 = star_type' env t2  in
                  FStar_Util.Inl uu____71399  in
                (uu____71390, FStar_Pervasives_Native.None)  in
              (uu____71370, uu____71373, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71343  in
          mk1 uu____71342
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____71487 =
            let uu____71488 =
              let uu____71515 = star_type' env e  in
              let uu____71518 =
                let uu____71535 =
                  let uu____71544 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____71544  in
                (uu____71535, FStar_Pervasives_Native.None)  in
              (uu____71515, uu____71518, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71488  in
          mk1 uu____71487
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____71585,(uu____71586,FStar_Pervasives_Native.Some uu____71587),uu____71588)
          ->
          let uu____71637 =
            let uu____71643 =
              let uu____71645 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____71645
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71643)  in
          FStar_Errors.raise_err uu____71637
      | FStar_Syntax_Syntax.Tm_refine uu____71649 ->
          let uu____71656 =
            let uu____71662 =
              let uu____71664 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____71664
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71662)  in
          FStar_Errors.raise_err uu____71656
      | FStar_Syntax_Syntax.Tm_uinst uu____71668 ->
          let uu____71675 =
            let uu____71681 =
              let uu____71683 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____71683
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71681)  in
          FStar_Errors.raise_err uu____71675
      | FStar_Syntax_Syntax.Tm_quoted uu____71687 ->
          let uu____71694 =
            let uu____71700 =
              let uu____71702 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____71702
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71700)  in
          FStar_Errors.raise_err uu____71694
      | FStar_Syntax_Syntax.Tm_constant uu____71706 ->
          let uu____71707 =
            let uu____71713 =
              let uu____71715 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____71715
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71713)  in
          FStar_Errors.raise_err uu____71707
      | FStar_Syntax_Syntax.Tm_match uu____71719 ->
          let uu____71742 =
            let uu____71748 =
              let uu____71750 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____71750
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71748)  in
          FStar_Errors.raise_err uu____71742
      | FStar_Syntax_Syntax.Tm_let uu____71754 ->
          let uu____71768 =
            let uu____71774 =
              let uu____71776 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____71776
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71774)  in
          FStar_Errors.raise_err uu____71768
      | FStar_Syntax_Syntax.Tm_uvar uu____71780 ->
          let uu____71793 =
            let uu____71799 =
              let uu____71801 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____71801
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71799)  in
          FStar_Errors.raise_err uu____71793
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71805 =
            let uu____71811 =
              let uu____71813 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____71813
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71811)  in
          FStar_Errors.raise_err uu____71805
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71818 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____71818
      | FStar_Syntax_Syntax.Tm_delayed uu____71821 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_71853  ->
    match uu___588_71853 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_71864  ->
                match uu___587_71864 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____71867 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____71877 =
      let uu____71878 = FStar_Syntax_Subst.compress t  in
      uu____71878.FStar_Syntax_Syntax.n  in
    match uu____71877 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____71910 =
            let uu____71911 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____71911  in
          is_C uu____71910  in
        if r
        then
          ((let uu____71935 =
              let uu____71937 =
                FStar_List.for_all
                  (fun uu____71948  ->
                     match uu____71948 with | (h,uu____71957) -> is_C h) args
                 in
              Prims.op_Negation uu____71937  in
            if uu____71935 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____71970 =
              let uu____71972 =
                FStar_List.for_all
                  (fun uu____71984  ->
                     match uu____71984 with
                     | (h,uu____71993) ->
                         let uu____71998 = is_C h  in
                         Prims.op_Negation uu____71998) args
                 in
              Prims.op_Negation uu____71972  in
            if uu____71970 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____72027 = nm_of_comp comp  in
        (match uu____72027 with
         | M t1 ->
             ((let uu____72031 = is_C t1  in
               if uu____72031 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____72040) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____72046) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____72052,uu____72053) -> is_C t1
    | uu____72094 -> false
  
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
          let uu____72130 =
            let uu____72131 =
              let uu____72148 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____72151 =
                let uu____72162 =
                  let uu____72171 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____72171)  in
                [uu____72162]  in
              (uu____72148, uu____72151)  in
            FStar_Syntax_Syntax.Tm_app uu____72131  in
          mk1 uu____72130  in
        let uu____72207 =
          let uu____72208 = FStar_Syntax_Syntax.mk_binder p  in [uu____72208]
           in
        FStar_Syntax_Util.abs uu____72207 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_72233  ->
    match uu___589_72233 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____72236 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____72474 =
          match uu____72474 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____72511 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____72514 =
                       let uu____72516 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____72516  in
                     Prims.op_Negation uu____72514)
                   in
                if uu____72511
                then
                  let uu____72518 =
                    let uu____72524 =
                      let uu____72526 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____72528 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____72530 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____72526 uu____72528 uu____72530
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____72524)  in
                  FStar_Errors.raise_err uu____72518
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____72555 = mk_return env t1 s_e  in
                     ((M t1), uu____72555, u_e)))
               | (M t1,N t2) ->
                   let uu____72562 =
                     let uu____72568 =
                       let uu____72570 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____72572 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____72574 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____72570 uu____72572 uu____72574
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____72568)
                      in
                   FStar_Errors.raise_err uu____72562)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_72626 =
            match uu___590_72626 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____72642 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____72663 =
                let uu____72669 =
                  let uu____72671 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____72671
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____72669)  in
              FStar_Errors.raise_error uu____72663 e2.FStar_Syntax_Syntax.pos
          | M uu____72681 ->
              let uu____72682 = check env1 e2 context_nm  in
              strip_m uu____72682
           in
        let uu____72689 =
          let uu____72690 = FStar_Syntax_Subst.compress e  in
          uu____72690.FStar_Syntax_Syntax.n  in
        match uu____72689 with
        | FStar_Syntax_Syntax.Tm_bvar uu____72699 ->
            let uu____72700 = infer env e  in return_if uu____72700
        | FStar_Syntax_Syntax.Tm_name uu____72707 ->
            let uu____72708 = infer env e  in return_if uu____72708
        | FStar_Syntax_Syntax.Tm_fvar uu____72715 ->
            let uu____72716 = infer env e  in return_if uu____72716
        | FStar_Syntax_Syntax.Tm_abs uu____72723 ->
            let uu____72742 = infer env e  in return_if uu____72742
        | FStar_Syntax_Syntax.Tm_constant uu____72749 ->
            let uu____72750 = infer env e  in return_if uu____72750
        | FStar_Syntax_Syntax.Tm_quoted uu____72757 ->
            let uu____72764 = infer env e  in return_if uu____72764
        | FStar_Syntax_Syntax.Tm_app uu____72771 ->
            let uu____72788 = infer env e  in return_if uu____72788
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____72796 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____72796 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____72861) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____72867) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____72873,uu____72874) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____72915 ->
            let uu____72929 =
              let uu____72931 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____72931  in
            failwith uu____72929
        | FStar_Syntax_Syntax.Tm_type uu____72940 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____72948 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____72970 ->
            let uu____72977 =
              let uu____72979 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____72979  in
            failwith uu____72977
        | FStar_Syntax_Syntax.Tm_uvar uu____72988 ->
            let uu____73001 =
              let uu____73003 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____73003  in
            failwith uu____73001
        | FStar_Syntax_Syntax.Tm_delayed uu____73012 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____73042 =
              let uu____73044 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____73044  in
            failwith uu____73042

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
      let uu____73074 =
        let uu____73075 = FStar_Syntax_Subst.compress e  in
        uu____73075.FStar_Syntax_Syntax.n  in
      match uu____73074 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____73094 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____73094
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____73145;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____73146;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____73152 =
                  let uu___1360_73153 = rc  in
                  let uu____73154 =
                    let uu____73159 =
                      let uu____73162 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____73162  in
                    FStar_Pervasives_Native.Some uu____73159  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_73153.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____73154;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_73153.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____73152
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_73174 = env  in
            let uu____73175 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____73175;
              subst = (uu___1366_73174.subst);
              tc_const = (uu___1366_73174.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____73201  ->
                 match uu____73201 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_73224 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_73224.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_73224.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____73225 =
            FStar_List.fold_left
              (fun uu____73256  ->
                 fun uu____73257  ->
                   match (uu____73256, uu____73257) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____73315 = is_C c  in
                       if uu____73315
                       then
                         let xw =
                           let uu____73325 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____73325
                            in
                         let x =
                           let uu___1385_73328 = bv  in
                           let uu____73329 =
                             let uu____73332 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____73332  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_73328.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_73328.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____73329
                           }  in
                         let env3 =
                           let uu___1388_73334 = env2  in
                           let uu____73335 =
                             let uu____73338 =
                               let uu____73339 =
                                 let uu____73346 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____73346)  in
                               FStar_Syntax_Syntax.NT uu____73339  in
                             uu____73338 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_73334.tcenv);
                             subst = uu____73335;
                             tc_const = (uu___1388_73334.tc_const)
                           }  in
                         let uu____73351 =
                           let uu____73354 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____73355 =
                             let uu____73358 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____73358 :: acc  in
                           uu____73354 :: uu____73355  in
                         (env3, uu____73351)
                       else
                         (let x =
                            let uu___1391_73364 = bv  in
                            let uu____73365 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_73364.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_73364.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____73365
                            }  in
                          let uu____73368 =
                            let uu____73371 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____73371 :: acc  in
                          (env2, uu____73368))) (env1, []) binders1
             in
          (match uu____73225 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____73391 =
                 let check_what =
                   let uu____73417 = is_monadic rc_opt1  in
                   if uu____73417 then check_m else check_n  in
                 let uu____73434 = check_what env2 body1  in
                 match uu____73434 with
                 | (t,s_body,u_body) ->
                     let uu____73454 =
                       let uu____73457 =
                         let uu____73458 = is_monadic rc_opt1  in
                         if uu____73458 then M t else N t  in
                       comp_of_nm uu____73457  in
                     (uu____73454, s_body, u_body)
                  in
               (match uu____73391 with
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
                                 let uu____73498 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_73504  ->
                                           match uu___591_73504 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____73507 -> false))
                                    in
                                 if uu____73498
                                 then
                                   let uu____73510 =
                                     FStar_List.filter
                                       (fun uu___592_73514  ->
                                          match uu___592_73514 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____73517 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____73510
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____73528 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_73534  ->
                                         match uu___593_73534 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____73537 -> false))
                                  in
                               if uu____73528
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_73546  ->
                                        match uu___594_73546 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____73549 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____73551 =
                                   let uu____73552 =
                                     let uu____73557 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____73557
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____73552 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____73551
                               else
                                 (let uu____73564 =
                                    let uu___1432_73565 = rc  in
                                    let uu____73566 =
                                      let uu____73571 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____73571
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_73565.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____73566;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_73565.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____73564))
                       in
                    let uu____73576 =
                      let comp1 =
                        let uu____73584 = is_monadic rc_opt1  in
                        let uu____73586 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____73584 uu____73586
                         in
                      let uu____73587 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____73587,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____73576 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____73625 =
                             let uu____73626 =
                               let uu____73645 =
                                 let uu____73648 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____73648 s_rc_opt  in
                               (s_binders1, s_body1, uu____73645)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73626  in
                           mk1 uu____73625  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____73668 =
                             let uu____73669 =
                               let uu____73688 =
                                 let uu____73691 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____73691 u_rc_opt  in
                               (u_binders2, u_body2, uu____73688)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73669  in
                           mk1 uu____73668  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____73707;_};
            FStar_Syntax_Syntax.fv_delta = uu____73708;
            FStar_Syntax_Syntax.fv_qual = uu____73709;_}
          ->
          let uu____73712 =
            let uu____73717 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____73717  in
          (match uu____73712 with
           | (uu____73748,t) ->
               let uu____73750 =
                 let uu____73751 = normalize1 t  in N uu____73751  in
               (uu____73750, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____73752;
             FStar_Syntax_Syntax.vars = uu____73753;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73832 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73832 with
           | (unary_op1,uu____73856) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____73927;
             FStar_Syntax_Syntax.vars = uu____73928;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____74024 = FStar_Syntax_Util.head_and_args e  in
          (match uu____74024 with
           | (unary_op1,uu____74048) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74127;
             FStar_Syntax_Syntax.vars = uu____74128;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____74166 = infer env a  in
          (match uu____74166 with
           | (t,s,u) ->
               let uu____74182 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74182 with
                | (head1,uu____74206) ->
                    let uu____74231 =
                      let uu____74232 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____74232  in
                    let uu____74233 =
                      let uu____74234 =
                        let uu____74235 =
                          let uu____74252 =
                            let uu____74263 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74263]  in
                          (head1, uu____74252)  in
                        FStar_Syntax_Syntax.Tm_app uu____74235  in
                      mk1 uu____74234  in
                    let uu____74300 =
                      let uu____74301 =
                        let uu____74302 =
                          let uu____74319 =
                            let uu____74330 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74330]  in
                          (head1, uu____74319)  in
                        FStar_Syntax_Syntax.Tm_app uu____74302  in
                      mk1 uu____74301  in
                    (uu____74231, uu____74233, uu____74300)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74367;
             FStar_Syntax_Syntax.vars = uu____74368;_},(a1,uu____74370)::a2::[])
          ->
          let uu____74426 = infer env a1  in
          (match uu____74426 with
           | (t,s,u) ->
               let uu____74442 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74442 with
                | (head1,uu____74466) ->
                    let uu____74491 =
                      let uu____74492 =
                        let uu____74493 =
                          let uu____74510 =
                            let uu____74521 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74521; a2]  in
                          (head1, uu____74510)  in
                        FStar_Syntax_Syntax.Tm_app uu____74493  in
                      mk1 uu____74492  in
                    let uu____74566 =
                      let uu____74567 =
                        let uu____74568 =
                          let uu____74585 =
                            let uu____74596 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74596; a2]  in
                          (head1, uu____74585)  in
                        FStar_Syntax_Syntax.Tm_app uu____74568  in
                      mk1 uu____74567  in
                    (t, uu____74491, uu____74566)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74641;
             FStar_Syntax_Syntax.vars = uu____74642;_},uu____74643)
          ->
          let uu____74668 =
            let uu____74674 =
              let uu____74676 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74676
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74674)  in
          FStar_Errors.raise_error uu____74668 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74686;
             FStar_Syntax_Syntax.vars = uu____74687;_},uu____74688)
          ->
          let uu____74713 =
            let uu____74719 =
              let uu____74721 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74721
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74719)  in
          FStar_Errors.raise_error uu____74713 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____74757 = check_n env head1  in
          (match uu____74757 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____74780 =
                   let uu____74781 = FStar_Syntax_Subst.compress t  in
                   uu____74781.FStar_Syntax_Syntax.n  in
                 match uu____74780 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____74785 -> true
                 | uu____74801 -> false  in
               let rec flatten1 t =
                 let uu____74823 =
                   let uu____74824 = FStar_Syntax_Subst.compress t  in
                   uu____74824.FStar_Syntax_Syntax.n  in
                 match uu____74823 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____74843);
                                FStar_Syntax_Syntax.pos = uu____74844;
                                FStar_Syntax_Syntax.vars = uu____74845;_})
                     when is_arrow t1 ->
                     let uu____74874 = flatten1 t1  in
                     (match uu____74874 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____74974,uu____74975) -> flatten1 e1
                 | uu____75016 ->
                     let uu____75017 =
                       let uu____75023 =
                         let uu____75025 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____75025
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____75023)  in
                     FStar_Errors.raise_err uu____75017
                  in
               let uu____75043 = flatten1 t_head  in
               (match uu____75043 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____75118 =
                          let uu____75124 =
                            let uu____75126 = FStar_Util.string_of_int n1  in
                            let uu____75134 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____75146 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____75126 uu____75134 uu____75146
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____75124)
                           in
                        FStar_Errors.raise_err uu____75118)
                     else ();
                     (let uu____75158 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____75158 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____75211 args1 =
                            match uu____75211 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____75311 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____75311
                                 | (binders3,[]) ->
                                     let uu____75349 =
                                       let uu____75350 =
                                         let uu____75353 =
                                           let uu____75354 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____75354
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____75353
                                          in
                                       uu____75350.FStar_Syntax_Syntax.n  in
                                     (match uu____75349 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____75387 =
                                            let uu____75388 =
                                              let uu____75389 =
                                                let uu____75404 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____75404)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____75389
                                               in
                                            mk1 uu____75388  in
                                          N uu____75387
                                      | uu____75417 -> failwith "wat?")
                                 | ([],uu____75419::uu____75420) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____75473)::binders3,(arg,uu____75476)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____75563 = FStar_List.splitAt n' binders1
                             in
                          (match uu____75563 with
                           | (binders2,uu____75601) ->
                               let uu____75634 =
                                 let uu____75657 =
                                   FStar_List.map2
                                     (fun uu____75719  ->
                                        fun uu____75720  ->
                                          match (uu____75719, uu____75720)
                                          with
                                          | ((bv,uu____75768),(arg,q)) ->
                                              let uu____75797 =
                                                let uu____75798 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____75798.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____75797 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____75819 ->
                                                   let uu____75820 =
                                                     let uu____75827 =
                                                       star_type' env arg  in
                                                     (uu____75827, q)  in
                                                   (uu____75820, [(arg, q)])
                                               | uu____75864 ->
                                                   let uu____75865 =
                                                     check_n env arg  in
                                                   (match uu____75865 with
                                                    | (uu____75890,s_arg,u_arg)
                                                        ->
                                                        let uu____75893 =
                                                          let uu____75902 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____75902
                                                          then
                                                            let uu____75913 =
                                                              let uu____75920
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____75920,
                                                                q)
                                                               in
                                                            [uu____75913;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____75893))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____75657  in
                               (match uu____75634 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____76048 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____76061 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____76048, uu____76061)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____76130) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____76136) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____76142,uu____76143) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____76185 =
            let uu____76186 = env.tc_const c  in N uu____76186  in
          (uu____76185, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____76193 ->
          let uu____76207 =
            let uu____76209 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____76209  in
          failwith uu____76207
      | FStar_Syntax_Syntax.Tm_type uu____76218 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____76226 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____76248 ->
          let uu____76255 =
            let uu____76257 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____76257  in
          failwith uu____76255
      | FStar_Syntax_Syntax.Tm_uvar uu____76266 ->
          let uu____76279 =
            let uu____76281 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____76281  in
          failwith uu____76279
      | FStar_Syntax_Syntax.Tm_delayed uu____76290 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____76320 =
            let uu____76322 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____76322  in
          failwith uu____76320

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
          let uu____76371 = check_n env e0  in
          match uu____76371 with
          | (uu____76384,s_e0,u_e0) ->
              let uu____76387 =
                let uu____76416 =
                  FStar_List.map
                    (fun b  ->
                       let uu____76477 = FStar_Syntax_Subst.open_branch b  in
                       match uu____76477 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_76519 = env  in
                             let uu____76520 =
                               let uu____76521 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____76521
                                in
                             {
                               tcenv = uu____76520;
                               subst = (uu___1707_76519.subst);
                               tc_const = (uu___1707_76519.tc_const)
                             }  in
                           let uu____76524 = f env1 body  in
                           (match uu____76524 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____76596 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____76416  in
              (match uu____76387 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____76702 = FStar_List.hd nms  in
                     match uu____76702 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_76711  ->
                          match uu___595_76711 with
                          | M uu____76713 -> true
                          | uu____76715 -> false) nms
                      in
                   let uu____76717 =
                     let uu____76754 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____76844  ->
                              match uu____76844 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____77028 =
                                         check env original_body (M t2)  in
                                       (match uu____77028 with
                                        | (uu____77065,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____77104,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____76754  in
                   (match uu____76717 with
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
                              (fun uu____77293  ->
                                 match uu____77293 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____77344 =
                                         let uu____77345 =
                                           let uu____77362 =
                                             let uu____77373 =
                                               let uu____77382 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____77385 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____77382, uu____77385)  in
                                             [uu____77373]  in
                                           (s_body, uu____77362)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____77345
                                          in
                                       mk1 uu____77344  in
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
                            let uu____77520 =
                              let uu____77521 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____77521]  in
                            let uu____77540 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____77520 uu____77540
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____77564 =
                              let uu____77573 =
                                let uu____77580 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____77580
                                 in
                              [uu____77573]  in
                            let uu____77599 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____77564 uu____77599
                             in
                          let uu____77602 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____77641 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____77602, uu____77641)
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
                           let uu____77751 =
                             let uu____77752 =
                               let uu____77753 =
                                 let uu____77780 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____77780,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____77753
                                in
                             mk1 uu____77752  in
                           let uu____77839 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____77751, uu____77839))))

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
              let uu____77904 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____77904]  in
            let uu____77923 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____77923 with
            | (x_binders1,e21) ->
                let uu____77936 = infer env e1  in
                (match uu____77936 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____77953 = is_C t1  in
                       if uu____77953
                       then
                         let uu___1793_77956 = binding  in
                         let uu____77957 =
                           let uu____77960 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____77960  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_77956.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_77956.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____77957;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_77956.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_77956.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_77956.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_77956.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_77964 = env  in
                       let uu____77965 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_77967 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_77967.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_77967.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____77965;
                         subst = (uu___1796_77964.subst);
                         tc_const = (uu___1796_77964.tc_const)
                       }  in
                     let uu____77968 = proceed env1 e21  in
                     (match uu____77968 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_77985 = binding  in
                            let uu____77986 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_77985.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_77985.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____77986;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_77985.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_77985.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_77985.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_77985.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____77989 =
                            let uu____77990 =
                              let uu____77991 =
                                let uu____78005 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_78022 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_78022.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_78022.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_78022.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_78022.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_78022.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_78022.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78005)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77991  in
                            mk1 uu____77990  in
                          let uu____78023 =
                            let uu____78024 =
                              let uu____78025 =
                                let uu____78039 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_78056 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_78056.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_78056.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_78056.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_78056.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_78056.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_78056.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78039)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78025  in
                            mk1 uu____78024  in
                          (nm_rec, uu____77989, uu____78023))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_78061 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_78061.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_78061.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_78061.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_78061.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_78061.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_78063 = env  in
                       let uu____78064 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_78066 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_78066.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_78066.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____78064;
                         subst = (uu___1820_78063.subst);
                         tc_const = (uu___1820_78063.tc_const)
                       }  in
                     let uu____78067 = ensure_m env1 e21  in
                     (match uu____78067 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____78091 =
                              let uu____78092 =
                                let uu____78109 =
                                  let uu____78120 =
                                    let uu____78129 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____78132 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78129, uu____78132)  in
                                  [uu____78120]  in
                                (s_e2, uu____78109)  in
                              FStar_Syntax_Syntax.Tm_app uu____78092  in
                            mk1 uu____78091  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____78174 =
                              let uu____78175 =
                                let uu____78192 =
                                  let uu____78203 =
                                    let uu____78212 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____78212)  in
                                  [uu____78203]  in
                                (s_e1, uu____78192)  in
                              FStar_Syntax_Syntax.Tm_app uu____78175  in
                            mk1 uu____78174  in
                          let uu____78248 =
                            let uu____78249 =
                              let uu____78250 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____78250]  in
                            FStar_Syntax_Util.abs uu____78249 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____78269 =
                            let uu____78270 =
                              let uu____78271 =
                                let uu____78285 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_78302 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_78302.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_78302.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_78302.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_78302.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_78302.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_78302.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78285)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78271  in
                            mk1 uu____78270  in
                          ((M t2), uu____78248, uu____78269)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78312 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____78312  in
      let uu____78313 = check env e mn  in
      match uu____78313 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78329 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78352 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____78352  in
      let uu____78353 = check env e mn  in
      match uu____78353 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78369 -> failwith "[check_m]: impossible"

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
        (let uu____78402 =
           let uu____78404 = is_C c  in Prims.op_Negation uu____78404  in
         if uu____78402 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____78418 =
           let uu____78419 = FStar_Syntax_Subst.compress c  in
           uu____78419.FStar_Syntax_Syntax.n  in
         match uu____78418 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____78448 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____78448 with
              | (wp_head,wp_args) ->
                  ((let uu____78492 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____78511 =
                           let uu____78513 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____78513
                            in
                         Prims.op_Negation uu____78511)
                       in
                    if uu____78492 then failwith "mismatch" else ());
                   (let uu____78526 =
                      let uu____78527 =
                        let uu____78544 =
                          FStar_List.map2
                            (fun uu____78582  ->
                               fun uu____78583  ->
                                 match (uu____78582, uu____78583) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____78645 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____78645
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____78654 =
                                         let uu____78656 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____78656 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____78654
                                       then
                                         let uu____78658 =
                                           let uu____78664 =
                                             let uu____78666 =
                                               print_implicit q  in
                                             let uu____78668 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____78666 uu____78668
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____78664)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____78658
                                       else ());
                                      (let uu____78674 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____78674, q)))) args wp_args
                           in
                        (head1, uu____78544)  in
                      FStar_Syntax_Syntax.Tm_app uu____78527  in
                    mk1 uu____78526)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____78720 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____78720 with
              | (binders_orig,comp1) ->
                  let uu____78727 =
                    let uu____78744 =
                      FStar_List.map
                        (fun uu____78784  ->
                           match uu____78784 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____78812 = is_C h  in
                               if uu____78812
                               then
                                 let w' =
                                   let uu____78828 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____78828
                                    in
                                 let uu____78830 =
                                   let uu____78839 =
                                     let uu____78848 =
                                       let uu____78855 =
                                         let uu____78856 =
                                           let uu____78857 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____78857  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____78856
                                          in
                                       (uu____78855, q)  in
                                     [uu____78848]  in
                                   (w', q) :: uu____78839  in
                                 (w', uu____78830)
                               else
                                 (let x =
                                    let uu____78891 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____78891
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____78744  in
                  (match uu____78727 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____78965 =
                           let uu____78968 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____78968
                            in
                         FStar_Syntax_Subst.subst_comp uu____78965 comp1  in
                       let app =
                         let uu____78972 =
                           let uu____78973 =
                             let uu____78990 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____79009 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____79010 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____79009, uu____79010)) bvs
                                in
                             (wp, uu____78990)  in
                           FStar_Syntax_Syntax.Tm_app uu____78973  in
                         mk1 uu____78972  in
                       let comp3 =
                         let uu____79025 = type_of_comp comp2  in
                         let uu____79026 = is_monadic_comp comp2  in
                         trans_G env uu____79025 uu____79026 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____79029,uu____79030) ->
             trans_F_ env e wp
         | uu____79071 -> failwith "impossible trans_F_")

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
            let uu____79079 =
              let uu____79080 = star_type' env h  in
              let uu____79083 =
                let uu____79094 =
                  let uu____79103 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____79103)  in
                [uu____79094]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____79080;
                FStar_Syntax_Syntax.effect_args = uu____79083;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____79079
          else
            (let uu____79129 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____79129)

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
    fun t  -> let uu____79150 = n env.tcenv t  in star_type' env uu____79150
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____79170 = n env.tcenv t  in check_n env uu____79170
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____79187 = n env.tcenv c  in
        let uu____79188 = n env.tcenv wp  in
        trans_F_ env uu____79187 uu____79188
  