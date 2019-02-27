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
              let uu___613_65801 = a  in
              let uu____65802 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_65801.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_65801.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____65802
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____65815 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____65815
             then
               (d "Elaborating extra WP combinators";
                (let uu____65821 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____65821))
             else ());
            (let rec collect_binders t =
               let uu____65840 =
                 let uu____65841 =
                   let uu____65844 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____65844
                    in
                 uu____65841.FStar_Syntax_Syntax.n  in
               match uu____65840 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____65879) -> t1
                     | uu____65888 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____65890 = collect_binders rest  in
                   FStar_List.append bs uu____65890
               | FStar_Syntax_Syntax.Tm_type uu____65905 -> []
               | uu____65912 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____65939 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____65939
                 FStar_Syntax_Util.name_binders
                in
             (let uu____65965 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____65965
              then
                let uu____65969 =
                  let uu____65971 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____65971  in
                d uu____65969
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____66009 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____66009 with
                | (sigelt,fv) ->
                    ((let uu____66017 =
                        let uu____66020 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____66020
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____66017);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____66144  ->
                     match uu____66144 with
                     | (t,b) ->
                         let uu____66158 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____66158))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____66197 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____66197))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____66231 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____66231)
                 in
              let uu____66234 =
                let uu____66251 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____66276 =
                        let uu____66279 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____66279  in
                      FStar_Syntax_Util.arrow gamma uu____66276  in
                    let uu____66280 =
                      let uu____66281 =
                        let uu____66290 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____66297 =
                          let uu____66306 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____66306]  in
                        uu____66290 :: uu____66297  in
                      FStar_List.append binders uu____66281  in
                    FStar_Syntax_Util.abs uu____66280 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____66337 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____66338 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____66337, uu____66338)  in
                match uu____66251 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____66380 =
                        let uu____66381 =
                          let uu____66398 =
                            let uu____66409 =
                              FStar_List.map
                                (fun uu____66431  ->
                                   match uu____66431 with
                                   | (bv,uu____66443) ->
                                       let uu____66448 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____66449 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____66448, uu____66449)) binders
                               in
                            let uu____66451 =
                              let uu____66458 =
                                let uu____66463 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____66464 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____66463, uu____66464)  in
                              let uu____66466 =
                                let uu____66473 =
                                  let uu____66478 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____66478)  in
                                [uu____66473]  in
                              uu____66458 :: uu____66466  in
                            FStar_List.append uu____66409 uu____66451  in
                          (fv, uu____66398)  in
                        FStar_Syntax_Syntax.Tm_app uu____66381  in
                      mk1 uu____66380  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____66234 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____66551 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____66551
                       in
                    let ret1 =
                      let uu____66556 =
                        let uu____66557 =
                          let uu____66560 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____66560  in
                        FStar_Syntax_Util.residual_tot uu____66557  in
                      FStar_Pervasives_Native.Some uu____66556  in
                    let body =
                      let uu____66564 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____66564 ret1  in
                    let uu____66567 =
                      let uu____66568 = mk_all_implicit binders  in
                      let uu____66575 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____66568 uu____66575  in
                    FStar_Syntax_Util.abs uu____66567 body ret1  in
                  let c_pure1 =
                    let uu____66613 = mk_lid "pure"  in
                    register env1 uu____66613 c_pure  in
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
                      let uu____66623 =
                        let uu____66624 =
                          let uu____66625 =
                            let uu____66634 =
                              let uu____66641 =
                                let uu____66642 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____66642
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____66641  in
                            [uu____66634]  in
                          let uu____66655 =
                            let uu____66658 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____66658  in
                          FStar_Syntax_Util.arrow uu____66625 uu____66655  in
                        mk_gctx uu____66624  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____66623
                       in
                    let r =
                      let uu____66661 =
                        let uu____66662 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66662  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____66661
                       in
                    let ret1 =
                      let uu____66667 =
                        let uu____66668 =
                          let uu____66671 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66671  in
                        FStar_Syntax_Util.residual_tot uu____66668  in
                      FStar_Pervasives_Native.Some uu____66667  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____66681 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____66684 =
                          let uu____66695 =
                            let uu____66698 =
                              let uu____66699 =
                                let uu____66700 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____66700
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____66699  in
                            [uu____66698]  in
                          FStar_List.append gamma_as_args uu____66695  in
                        FStar_Syntax_Util.mk_app uu____66681 uu____66684  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____66703 =
                      let uu____66704 = mk_all_implicit binders  in
                      let uu____66711 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____66704 uu____66711  in
                    FStar_Syntax_Util.abs uu____66703 outer_body ret1  in
                  let c_app1 =
                    let uu____66763 = mk_lid "app"  in
                    register env1 uu____66763 c_app  in
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
                      let uu____66775 =
                        let uu____66784 =
                          let uu____66791 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____66791  in
                        [uu____66784]  in
                      let uu____66804 =
                        let uu____66807 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____66807  in
                      FStar_Syntax_Util.arrow uu____66775 uu____66804  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____66811 =
                        let uu____66812 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66812  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____66811
                       in
                    let ret1 =
                      let uu____66817 =
                        let uu____66818 =
                          let uu____66821 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66821  in
                        FStar_Syntax_Util.residual_tot uu____66818  in
                      FStar_Pervasives_Native.Some uu____66817  in
                    let uu____66822 =
                      let uu____66823 = mk_all_implicit binders  in
                      let uu____66830 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____66823 uu____66830  in
                    let uu____66881 =
                      let uu____66884 =
                        let uu____66895 =
                          let uu____66898 =
                            let uu____66899 =
                              let uu____66910 =
                                let uu____66913 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____66913]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____66910
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____66899  in
                          let uu____66922 =
                            let uu____66925 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____66925]  in
                          uu____66898 :: uu____66922  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____66895
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____66884  in
                    FStar_Syntax_Util.abs uu____66822 uu____66881 ret1  in
                  let c_lift11 =
                    let uu____66935 = mk_lid "lift1"  in
                    register env1 uu____66935 c_lift1  in
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
                      let uu____66949 =
                        let uu____66958 =
                          let uu____66965 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____66965  in
                        let uu____66966 =
                          let uu____66975 =
                            let uu____66982 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____66982  in
                          [uu____66975]  in
                        uu____66958 :: uu____66966  in
                      let uu____67001 =
                        let uu____67004 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____67004  in
                      FStar_Syntax_Util.arrow uu____66949 uu____67001  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____67008 =
                        let uu____67009 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____67009  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____67008
                       in
                    let a2 =
                      let uu____67012 =
                        let uu____67013 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____67013  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____67012
                       in
                    let ret1 =
                      let uu____67018 =
                        let uu____67019 =
                          let uu____67022 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____67022  in
                        FStar_Syntax_Util.residual_tot uu____67019  in
                      FStar_Pervasives_Native.Some uu____67018  in
                    let uu____67023 =
                      let uu____67024 = mk_all_implicit binders  in
                      let uu____67031 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____67024 uu____67031  in
                    let uu____67096 =
                      let uu____67099 =
                        let uu____67110 =
                          let uu____67113 =
                            let uu____67114 =
                              let uu____67125 =
                                let uu____67128 =
                                  let uu____67129 =
                                    let uu____67140 =
                                      let uu____67143 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____67143]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____67140
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____67129
                                   in
                                let uu____67152 =
                                  let uu____67155 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____67155]  in
                                uu____67128 :: uu____67152  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67125
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____67114  in
                          let uu____67164 =
                            let uu____67167 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____67167]  in
                          uu____67113 :: uu____67164  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67110
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67099  in
                    FStar_Syntax_Util.abs uu____67023 uu____67096 ret1  in
                  let c_lift21 =
                    let uu____67177 = mk_lid "lift2"  in
                    register env1 uu____67177 c_lift2  in
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
                      let uu____67189 =
                        let uu____67198 =
                          let uu____67205 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67205  in
                        [uu____67198]  in
                      let uu____67218 =
                        let uu____67221 =
                          let uu____67222 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____67222  in
                        FStar_Syntax_Syntax.mk_Total uu____67221  in
                      FStar_Syntax_Util.arrow uu____67189 uu____67218  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____67228 =
                        let uu____67229 =
                          let uu____67232 =
                            let uu____67233 =
                              let uu____67242 =
                                let uu____67249 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____67249
                                 in
                              [uu____67242]  in
                            let uu____67262 =
                              let uu____67265 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____67265  in
                            FStar_Syntax_Util.arrow uu____67233 uu____67262
                             in
                          mk_ctx uu____67232  in
                        FStar_Syntax_Util.residual_tot uu____67229  in
                      FStar_Pervasives_Native.Some uu____67228  in
                    let e1 =
                      let uu____67267 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____67267
                       in
                    let body =
                      let uu____67272 =
                        let uu____67273 =
                          let uu____67282 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____67282]  in
                        FStar_List.append gamma uu____67273  in
                      let uu____67307 =
                        let uu____67310 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____67313 =
                          let uu____67324 =
                            let uu____67325 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____67325  in
                          let uu____67326 = args_of_binders1 gamma  in
                          uu____67324 :: uu____67326  in
                        FStar_Syntax_Util.mk_app uu____67310 uu____67313  in
                      FStar_Syntax_Util.abs uu____67272 uu____67307 ret1  in
                    let uu____67329 =
                      let uu____67330 = mk_all_implicit binders  in
                      let uu____67337 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____67330 uu____67337  in
                    FStar_Syntax_Util.abs uu____67329 body ret1  in
                  let c_push1 =
                    let uu____67382 = mk_lid "push"  in
                    register env1 uu____67382 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____67409 =
                        let uu____67410 =
                          let uu____67427 = args_of_binders1 binders  in
                          (c, uu____67427)  in
                        FStar_Syntax_Syntax.Tm_app uu____67410  in
                      mk1 uu____67409
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____67456 =
                        let uu____67457 =
                          let uu____67466 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____67473 =
                            let uu____67482 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____67482]  in
                          uu____67466 :: uu____67473  in
                        let uu____67507 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____67457 uu____67507  in
                      FStar_Syntax_Syntax.mk_Total uu____67456  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____67512 =
                      let uu____67513 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____67513  in
                    let uu____67528 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____67533 =
                        let uu____67536 =
                          let uu____67547 =
                            let uu____67550 =
                              let uu____67551 =
                                let uu____67562 =
                                  let uu____67571 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____67571  in
                                [uu____67562]  in
                              FStar_Syntax_Util.mk_app l_ite uu____67551  in
                            [uu____67550]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____67547
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____67536  in
                      FStar_Syntax_Util.ascribe uu____67533
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____67512 uu____67528
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____67615 = mk_lid "wp_if_then_else"  in
                    register env1 uu____67615 wp_if_then_else  in
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
                      let uu____67632 =
                        let uu____67643 =
                          let uu____67646 =
                            let uu____67647 =
                              let uu____67658 =
                                let uu____67661 =
                                  let uu____67662 =
                                    let uu____67673 =
                                      let uu____67682 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67682
                                       in
                                    [uu____67673]  in
                                  FStar_Syntax_Util.mk_app l_and uu____67662
                                   in
                                [uu____67661]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67658
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67647  in
                          let uu____67707 =
                            let uu____67710 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67710]  in
                          uu____67646 :: uu____67707  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67643
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67632  in
                    let uu____67719 =
                      let uu____67720 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67720  in
                    FStar_Syntax_Util.abs uu____67719 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____67736 = mk_lid "wp_assert"  in
                    register env1 uu____67736 wp_assert  in
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
                      let uu____67753 =
                        let uu____67764 =
                          let uu____67767 =
                            let uu____67768 =
                              let uu____67779 =
                                let uu____67782 =
                                  let uu____67783 =
                                    let uu____67794 =
                                      let uu____67803 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67803
                                       in
                                    [uu____67794]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____67783
                                   in
                                [uu____67782]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67779
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67768  in
                          let uu____67828 =
                            let uu____67831 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67831]  in
                          uu____67767 :: uu____67828  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67764
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67753  in
                    let uu____67840 =
                      let uu____67841 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67841  in
                    FStar_Syntax_Util.abs uu____67840 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____67857 = mk_lid "wp_assume"  in
                    register env1 uu____67857 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____67870 =
                        let uu____67879 =
                          let uu____67886 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____67886  in
                        [uu____67879]  in
                      let uu____67899 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____67870 uu____67899  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____67907 =
                        let uu____67918 =
                          let uu____67921 =
                            let uu____67922 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67922  in
                          let uu____67941 =
                            let uu____67944 =
                              let uu____67945 =
                                let uu____67956 =
                                  let uu____67959 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____67959]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____67956
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____67945
                               in
                            [uu____67944]  in
                          uu____67921 :: uu____67941  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67918
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67907  in
                    let uu____67976 =
                      let uu____67977 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____67977  in
                    FStar_Syntax_Util.abs uu____67976 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____67993 = mk_lid "wp_close"  in
                    register env1 uu____67993 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____68004 =
                      let uu____68005 =
                        let uu____68006 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____68006
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____68005
                       in
                    FStar_Pervasives_Native.Some uu____68004  in
                  let mk_forall1 x body =
                    let uu____68018 =
                      let uu____68025 =
                        let uu____68026 =
                          let uu____68043 =
                            let uu____68054 =
                              let uu____68063 =
                                let uu____68064 =
                                  let uu____68065 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____68065]  in
                                FStar_Syntax_Util.abs uu____68064 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____68063  in
                            [uu____68054]  in
                          (FStar_Syntax_Util.tforall, uu____68043)  in
                        FStar_Syntax_Syntax.Tm_app uu____68026  in
                      FStar_Syntax_Syntax.mk uu____68025  in
                    uu____68018 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____68126 =
                      let uu____68127 = FStar_Syntax_Subst.compress t  in
                      uu____68127.FStar_Syntax_Syntax.n  in
                    match uu____68126 with
                    | FStar_Syntax_Syntax.Tm_type uu____68131 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68164  ->
                              match uu____68164 with
                              | (b,uu____68173) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____68178 -> true  in
                  let rec is_monotonic t =
                    let uu____68191 =
                      let uu____68192 = FStar_Syntax_Subst.compress t  in
                      uu____68192.FStar_Syntax_Syntax.n  in
                    match uu____68191 with
                    | FStar_Syntax_Syntax.Tm_type uu____68196 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68229  ->
                              match uu____68229 with
                              | (b,uu____68238) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____68243 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____68317 =
                      let uu____68318 = FStar_Syntax_Subst.compress t1  in
                      uu____68318.FStar_Syntax_Syntax.n  in
                    match uu____68317 with
                    | FStar_Syntax_Syntax.Tm_type uu____68323 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____68326);
                                      FStar_Syntax_Syntax.pos = uu____68327;
                                      FStar_Syntax_Syntax.vars = uu____68328;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68372 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68372
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68382 =
                              let uu____68385 =
                                let uu____68396 =
                                  let uu____68405 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68405  in
                                [uu____68396]  in
                              FStar_Syntax_Util.mk_app x uu____68385  in
                            let uu____68422 =
                              let uu____68425 =
                                let uu____68436 =
                                  let uu____68445 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68445  in
                                [uu____68436]  in
                              FStar_Syntax_Util.mk_app y uu____68425  in
                            mk_rel1 b uu____68382 uu____68422  in
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
                             let uu____68469 =
                               let uu____68472 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68475 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68472 uu____68475  in
                             let uu____68478 =
                               let uu____68481 =
                                 let uu____68484 =
                                   let uu____68495 =
                                     let uu____68504 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68504
                                      in
                                   [uu____68495]  in
                                 FStar_Syntax_Util.mk_app x uu____68484  in
                               let uu____68521 =
                                 let uu____68524 =
                                   let uu____68535 =
                                     let uu____68544 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68544
                                      in
                                   [uu____68535]  in
                                 FStar_Syntax_Util.mk_app y uu____68524  in
                               mk_rel1 b uu____68481 uu____68521  in
                             FStar_Syntax_Util.mk_imp uu____68469 uu____68478
                              in
                           let uu____68561 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68561)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____68564);
                                      FStar_Syntax_Syntax.pos = uu____68565;
                                      FStar_Syntax_Syntax.vars = uu____68566;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68610 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68610
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68620 =
                              let uu____68623 =
                                let uu____68634 =
                                  let uu____68643 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68643  in
                                [uu____68634]  in
                              FStar_Syntax_Util.mk_app x uu____68623  in
                            let uu____68660 =
                              let uu____68663 =
                                let uu____68674 =
                                  let uu____68683 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68683  in
                                [uu____68674]  in
                              FStar_Syntax_Util.mk_app y uu____68663  in
                            mk_rel1 b uu____68620 uu____68660  in
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
                             let uu____68707 =
                               let uu____68710 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68713 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68710 uu____68713  in
                             let uu____68716 =
                               let uu____68719 =
                                 let uu____68722 =
                                   let uu____68733 =
                                     let uu____68742 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68742
                                      in
                                   [uu____68733]  in
                                 FStar_Syntax_Util.mk_app x uu____68722  in
                               let uu____68759 =
                                 let uu____68762 =
                                   let uu____68773 =
                                     let uu____68782 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68782
                                      in
                                   [uu____68773]  in
                                 FStar_Syntax_Util.mk_app y uu____68762  in
                               mk_rel1 b uu____68719 uu____68759  in
                             FStar_Syntax_Util.mk_imp uu____68707 uu____68716
                              in
                           let uu____68799 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68799)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_68838 = t1  in
                          let uu____68839 =
                            let uu____68840 =
                              let uu____68855 =
                                let uu____68858 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____68858  in
                              ([binder], uu____68855)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____68840  in
                          {
                            FStar_Syntax_Syntax.n = uu____68839;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_68838.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_68838.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____68881 ->
                        failwith "unhandled arrow"
                    | uu____68899 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____68936 =
                        let uu____68937 = FStar_Syntax_Subst.compress t1  in
                        uu____68937.FStar_Syntax_Syntax.n  in
                      match uu____68936 with
                      | FStar_Syntax_Syntax.Tm_type uu____68940 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____68967 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____68967
                          ->
                          let project i tuple =
                            let projector =
                              let uu____68988 =
                                let uu____68989 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____68989 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____68988
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____69019 =
                            let uu____69030 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____69048  ->
                                     match uu____69048 with
                                     | (t2,q) ->
                                         let uu____69068 = project i x  in
                                         let uu____69071 = project i y  in
                                         mk_stronger t2 uu____69068
                                           uu____69071) args
                               in
                            match uu____69030 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____69019 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____69125);
                                      FStar_Syntax_Syntax.pos = uu____69126;
                                      FStar_Syntax_Syntax.vars = uu____69127;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69171  ->
                                   match uu____69171 with
                                   | (bv,q) ->
                                       let uu____69185 =
                                         let uu____69187 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69187  in
                                       FStar_Syntax_Syntax.gen_bv uu____69185
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69196 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69196) bvs
                             in
                          let body =
                            let uu____69198 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69201 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69198 uu____69201  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____69210);
                                      FStar_Syntax_Syntax.pos = uu____69211;
                                      FStar_Syntax_Syntax.vars = uu____69212;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69256  ->
                                   match uu____69256 with
                                   | (bv,q) ->
                                       let uu____69270 =
                                         let uu____69272 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69272  in
                                       FStar_Syntax_Syntax.gen_bv uu____69270
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69281 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69281) bvs
                             in
                          let body =
                            let uu____69283 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69286 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69283 uu____69286  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____69293 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____69296 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____69299 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____69302 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____69296 uu____69299 uu____69302  in
                    let uu____69305 =
                      let uu____69306 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____69306  in
                    FStar_Syntax_Util.abs uu____69305 body ret_tot_type  in
                  let stronger1 =
                    let uu____69348 = mk_lid "stronger"  in
                    register env1 uu____69348 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69356 = FStar_Util.prefix gamma  in
                    match uu____69356 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____69422 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____69422
                             in
                          let uu____69427 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____69427 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____69437 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____69437  in
                              let guard_free1 =
                                let uu____69449 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____69449  in
                              let pat =
                                let uu____69453 =
                                  let uu____69464 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____69464]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____69453
                                 in
                              let pattern_guarded_body =
                                let uu____69492 =
                                  let uu____69493 =
                                    let uu____69500 =
                                      let uu____69501 =
                                        let uu____69514 =
                                          let uu____69525 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____69525]  in
                                        [uu____69514]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____69501
                                       in
                                    (body, uu____69500)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____69493  in
                                mk1 uu____69492  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____69572 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____69581 =
                            let uu____69584 =
                              let uu____69585 =
                                let uu____69588 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____69591 =
                                  let uu____69602 = args_of_binders1 wp_args
                                     in
                                  let uu____69605 =
                                    let uu____69608 =
                                      let uu____69609 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____69609
                                       in
                                    [uu____69608]  in
                                  FStar_List.append uu____69602 uu____69605
                                   in
                                FStar_Syntax_Util.mk_app uu____69588
                                  uu____69591
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____69585  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____69584
                             in
                          FStar_Syntax_Util.abs gamma uu____69581
                            ret_gtot_type
                           in
                        let uu____69610 =
                          let uu____69611 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____69611  in
                        FStar_Syntax_Util.abs uu____69610 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____69627 = mk_lid "ite_wp"  in
                    register env1 uu____69627 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69635 = FStar_Util.prefix gamma  in
                    match uu____69635 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____69693 =
                            let uu____69694 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____69701 =
                              let uu____69712 =
                                let uu____69721 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____69721  in
                              [uu____69712]  in
                            FStar_Syntax_Util.mk_app uu____69694 uu____69701
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____69693
                           in
                        let uu____69738 =
                          let uu____69739 =
                            let uu____69748 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____69748 gamma  in
                          FStar_List.append binders uu____69739  in
                        FStar_Syntax_Util.abs uu____69738 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____69770 = mk_lid "null_wp"  in
                    register env1 uu____69770 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____69783 =
                        let uu____69794 =
                          let uu____69797 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____69798 =
                            let uu____69801 =
                              let uu____69802 =
                                let uu____69813 =
                                  let uu____69822 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____69822  in
                                [uu____69813]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____69802
                               in
                            let uu____69839 =
                              let uu____69842 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____69842]  in
                            uu____69801 :: uu____69839  in
                          uu____69797 :: uu____69798  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____69794
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____69783  in
                    let uu____69851 =
                      let uu____69852 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____69852  in
                    FStar_Syntax_Util.abs uu____69851 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____69868 = mk_lid "wp_trivial"  in
                    register env1 uu____69868 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____69874 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____69874
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____69886 =
                      let uu____69887 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____69887  in
                    let uu____69935 =
                      let uu___934_69936 = ed  in
                      let uu____69937 =
                        let uu____69938 = c wp_if_then_else2  in
                        ([], uu____69938)  in
                      let uu____69945 =
                        let uu____69946 = c ite_wp2  in ([], uu____69946)  in
                      let uu____69953 =
                        let uu____69954 = c stronger2  in ([], uu____69954)
                         in
                      let uu____69961 =
                        let uu____69962 = c wp_close2  in ([], uu____69962)
                         in
                      let uu____69969 =
                        let uu____69970 = c wp_assert2  in ([], uu____69970)
                         in
                      let uu____69977 =
                        let uu____69978 = c wp_assume2  in ([], uu____69978)
                         in
                      let uu____69985 =
                        let uu____69986 = c null_wp2  in ([], uu____69986)
                         in
                      let uu____69993 =
                        let uu____69994 = c wp_trivial2  in ([], uu____69994)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_69936.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_69936.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_69936.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_69936.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_69936.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_69936.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_69936.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____69937;
                        FStar_Syntax_Syntax.ite_wp = uu____69945;
                        FStar_Syntax_Syntax.stronger = uu____69953;
                        FStar_Syntax_Syntax.close_wp = uu____69961;
                        FStar_Syntax_Syntax.assert_p = uu____69969;
                        FStar_Syntax_Syntax.assume_p = uu____69977;
                        FStar_Syntax_Syntax.null_wp = uu____69985;
                        FStar_Syntax_Syntax.trivial = uu____69993;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_69936.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_69936.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_69936.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_69936.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_69936.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____69886, uu____69935)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_70018 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_70018.subst);
        tc_const = (uu___939_70018.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____70039 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____70059 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____70080) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_70094  ->
                match uu___585_70094 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____70097 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____70099 ->
        let uu____70100 =
          let uu____70106 =
            let uu____70108 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____70108
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____70106)  in
        FStar_Errors.raise_error uu____70100 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_70118  ->
    match uu___586_70118 with
    | N t ->
        let uu____70121 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____70121
    | M t ->
        let uu____70125 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____70125
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____70134,c) -> nm_of_comp c
    | uu____70156 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____70169 = nm_of_comp c  in
    match uu____70169 with | M uu____70171 -> true | N uu____70173 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____70184 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____70200 =
        let uu____70209 =
          let uu____70216 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____70216  in
        [uu____70209]  in
      let uu____70235 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____70200 uu____70235  in
    let uu____70238 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____70238
  
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
        let uu____70280 =
          let uu____70281 =
            let uu____70296 =
              let uu____70305 =
                let uu____70312 =
                  let uu____70313 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____70313  in
                let uu____70314 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____70312, uu____70314)  in
              [uu____70305]  in
            let uu____70332 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____70296, uu____70332)  in
          FStar_Syntax_Syntax.Tm_arrow uu____70281  in
        mk1 uu____70280

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70372) ->
          let binders1 =
            FStar_List.map
              (fun uu____70418  ->
                 match uu____70418 with
                 | (bv,aqual) ->
                     let uu____70437 =
                       let uu___989_70438 = bv  in
                       let uu____70439 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_70438.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_70438.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____70439
                       }  in
                     (uu____70437, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____70444,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____70446);
                              FStar_Syntax_Syntax.pos = uu____70447;
                              FStar_Syntax_Syntax.vars = uu____70448;_})
               ->
               let uu____70477 =
                 let uu____70478 =
                   let uu____70493 =
                     let uu____70496 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____70496  in
                   (binders1, uu____70493)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____70478  in
               mk1 uu____70477
           | uu____70507 ->
               let uu____70508 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____70508 with
                | N hn ->
                    let uu____70510 =
                      let uu____70511 =
                        let uu____70526 =
                          let uu____70529 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____70529  in
                        (binders1, uu____70526)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70511  in
                    mk1 uu____70510
                | M a ->
                    let uu____70541 =
                      let uu____70542 =
                        let uu____70557 =
                          let uu____70566 =
                            let uu____70575 =
                              let uu____70582 =
                                let uu____70583 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____70583  in
                              let uu____70584 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____70582, uu____70584)  in
                            [uu____70575]  in
                          FStar_List.append binders1 uu____70566  in
                        let uu____70608 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____70557, uu____70608)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70542  in
                    mk1 uu____70541))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____70702 = f x  in
                    FStar_Util.string_builder_append strb uu____70702);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____70711 = f x1  in
                         FStar_Util.string_builder_append strb uu____70711))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____70715 =
              let uu____70721 =
                let uu____70723 = FStar_Syntax_Print.term_to_string t2  in
                let uu____70725 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____70723 uu____70725
                 in
              (FStar_Errors.Warning_DependencyFound, uu____70721)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____70715  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____70747 =
              let uu____70748 = FStar_Syntax_Subst.compress ty  in
              uu____70748.FStar_Syntax_Syntax.n  in
            match uu____70747 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____70774 =
                  let uu____70776 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____70776  in
                if uu____70774
                then false
                else
                  (try
                     (fun uu___1038_70793  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____70817 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____70817 s  in
                              let uu____70820 =
                                let uu____70822 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____70822  in
                              if uu____70820
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____70828 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____70828 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____70853  ->
                                          match uu____70853 with
                                          | (bv,uu____70865) ->
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
            | uu____70893 ->
                ((let uu____70895 =
                    let uu____70901 =
                      let uu____70903 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____70903
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____70901)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____70895);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____70919 =
              let uu____70920 = FStar_Syntax_Subst.compress head2  in
              uu____70920.FStar_Syntax_Syntax.n  in
            match uu____70919 with
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
                  (let uu____70926 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____70926)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____70929 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____70929 with
                 | ((uu____70939,ty),uu____70941) ->
                     let uu____70946 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____70946
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____70959 =
                         let uu____70960 = FStar_Syntax_Subst.compress res
                            in
                         uu____70960.FStar_Syntax_Syntax.n  in
                       (match uu____70959 with
                        | FStar_Syntax_Syntax.Tm_app uu____70964 -> true
                        | uu____70982 ->
                            ((let uu____70984 =
                                let uu____70990 =
                                  let uu____70992 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____70992
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____70990)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____70984);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____71000 -> true
            | FStar_Syntax_Syntax.Tm_name uu____71002 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71005) ->
                is_valid_application t2
            | uu____71010 -> false  in
          let uu____71012 = is_valid_application head1  in
          if uu____71012
          then
            let uu____71015 =
              let uu____71016 =
                let uu____71033 =
                  FStar_List.map
                    (fun uu____71062  ->
                       match uu____71062 with
                       | (t2,qual) ->
                           let uu____71087 = star_type' env t2  in
                           (uu____71087, qual)) args
                   in
                (head1, uu____71033)  in
              FStar_Syntax_Syntax.Tm_app uu____71016  in
            mk1 uu____71015
          else
            (let uu____71104 =
               let uu____71110 =
                 let uu____71112 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____71112
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____71110)  in
             FStar_Errors.raise_err uu____71104)
      | FStar_Syntax_Syntax.Tm_bvar uu____71116 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____71117 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____71118 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____71119 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____71147 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____71147 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_71155 = env  in
                 let uu____71156 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____71156;
                   subst = (uu___1110_71155.subst);
                   tc_const = (uu___1110_71155.tc_const)
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
               ((let uu___1125_71183 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_71183.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_71183.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____71190 =
            let uu____71191 =
              let uu____71198 = star_type' env t2  in (uu____71198, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____71191  in
          mk1 uu____71190
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____71250 =
            let uu____71251 =
              let uu____71278 = star_type' env e  in
              let uu____71281 =
                let uu____71298 =
                  let uu____71307 = star_type' env t2  in
                  FStar_Util.Inl uu____71307  in
                (uu____71298, FStar_Pervasives_Native.None)  in
              (uu____71278, uu____71281, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71251  in
          mk1 uu____71250
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____71395 =
            let uu____71396 =
              let uu____71423 = star_type' env e  in
              let uu____71426 =
                let uu____71443 =
                  let uu____71452 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____71452  in
                (uu____71443, FStar_Pervasives_Native.None)  in
              (uu____71423, uu____71426, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71396  in
          mk1 uu____71395
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____71493,(uu____71494,FStar_Pervasives_Native.Some uu____71495),uu____71496)
          ->
          let uu____71545 =
            let uu____71551 =
              let uu____71553 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____71553
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71551)  in
          FStar_Errors.raise_err uu____71545
      | FStar_Syntax_Syntax.Tm_refine uu____71557 ->
          let uu____71564 =
            let uu____71570 =
              let uu____71572 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____71572
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71570)  in
          FStar_Errors.raise_err uu____71564
      | FStar_Syntax_Syntax.Tm_uinst uu____71576 ->
          let uu____71583 =
            let uu____71589 =
              let uu____71591 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____71591
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71589)  in
          FStar_Errors.raise_err uu____71583
      | FStar_Syntax_Syntax.Tm_quoted uu____71595 ->
          let uu____71602 =
            let uu____71608 =
              let uu____71610 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____71610
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71608)  in
          FStar_Errors.raise_err uu____71602
      | FStar_Syntax_Syntax.Tm_constant uu____71614 ->
          let uu____71615 =
            let uu____71621 =
              let uu____71623 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____71623
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71621)  in
          FStar_Errors.raise_err uu____71615
      | FStar_Syntax_Syntax.Tm_match uu____71627 ->
          let uu____71650 =
            let uu____71656 =
              let uu____71658 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____71658
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71656)  in
          FStar_Errors.raise_err uu____71650
      | FStar_Syntax_Syntax.Tm_let uu____71662 ->
          let uu____71676 =
            let uu____71682 =
              let uu____71684 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____71684
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71682)  in
          FStar_Errors.raise_err uu____71676
      | FStar_Syntax_Syntax.Tm_uvar uu____71688 ->
          let uu____71701 =
            let uu____71707 =
              let uu____71709 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____71709
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71707)  in
          FStar_Errors.raise_err uu____71701
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71713 =
            let uu____71719 =
              let uu____71721 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____71721
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71719)  in
          FStar_Errors.raise_err uu____71713
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71726 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____71726
      | FStar_Syntax_Syntax.Tm_delayed uu____71729 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_71761  ->
    match uu___588_71761 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_71772  ->
                match uu___587_71772 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____71775 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____71785 =
      let uu____71786 = FStar_Syntax_Subst.compress t  in
      uu____71786.FStar_Syntax_Syntax.n  in
    match uu____71785 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____71818 =
            let uu____71819 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____71819  in
          is_C uu____71818  in
        if r
        then
          ((let uu____71843 =
              let uu____71845 =
                FStar_List.for_all
                  (fun uu____71856  ->
                     match uu____71856 with | (h,uu____71865) -> is_C h) args
                 in
              Prims.op_Negation uu____71845  in
            if uu____71843 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____71878 =
              let uu____71880 =
                FStar_List.for_all
                  (fun uu____71892  ->
                     match uu____71892 with
                     | (h,uu____71901) ->
                         let uu____71906 = is_C h  in
                         Prims.op_Negation uu____71906) args
                 in
              Prims.op_Negation uu____71880  in
            if uu____71878 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____71935 = nm_of_comp comp  in
        (match uu____71935 with
         | M t1 ->
             ((let uu____71939 = is_C t1  in
               if uu____71939 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____71948) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____71954) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____71960,uu____71961) -> is_C t1
    | uu____72002 -> false
  
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
          let uu____72038 =
            let uu____72039 =
              let uu____72056 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____72059 =
                let uu____72070 =
                  let uu____72079 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____72079)  in
                [uu____72070]  in
              (uu____72056, uu____72059)  in
            FStar_Syntax_Syntax.Tm_app uu____72039  in
          mk1 uu____72038  in
        let uu____72115 =
          let uu____72116 = FStar_Syntax_Syntax.mk_binder p  in [uu____72116]
           in
        FStar_Syntax_Util.abs uu____72115 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_72141  ->
    match uu___589_72141 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____72144 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____72382 =
          match uu____72382 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____72419 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____72422 =
                       let uu____72424 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____72424  in
                     Prims.op_Negation uu____72422)
                   in
                if uu____72419
                then
                  let uu____72426 =
                    let uu____72432 =
                      let uu____72434 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____72436 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____72438 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____72434 uu____72436 uu____72438
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____72432)  in
                  FStar_Errors.raise_err uu____72426
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____72463 = mk_return env t1 s_e  in
                     ((M t1), uu____72463, u_e)))
               | (M t1,N t2) ->
                   let uu____72470 =
                     let uu____72476 =
                       let uu____72478 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____72480 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____72482 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____72478 uu____72480 uu____72482
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____72476)
                      in
                   FStar_Errors.raise_err uu____72470)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_72534 =
            match uu___590_72534 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____72550 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____72571 =
                let uu____72577 =
                  let uu____72579 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____72579
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____72577)  in
              FStar_Errors.raise_error uu____72571 e2.FStar_Syntax_Syntax.pos
          | M uu____72589 ->
              let uu____72590 = check env1 e2 context_nm  in
              strip_m uu____72590
           in
        let uu____72597 =
          let uu____72598 = FStar_Syntax_Subst.compress e  in
          uu____72598.FStar_Syntax_Syntax.n  in
        match uu____72597 with
        | FStar_Syntax_Syntax.Tm_bvar uu____72607 ->
            let uu____72608 = infer env e  in return_if uu____72608
        | FStar_Syntax_Syntax.Tm_name uu____72615 ->
            let uu____72616 = infer env e  in return_if uu____72616
        | FStar_Syntax_Syntax.Tm_fvar uu____72623 ->
            let uu____72624 = infer env e  in return_if uu____72624
        | FStar_Syntax_Syntax.Tm_abs uu____72631 ->
            let uu____72650 = infer env e  in return_if uu____72650
        | FStar_Syntax_Syntax.Tm_constant uu____72657 ->
            let uu____72658 = infer env e  in return_if uu____72658
        | FStar_Syntax_Syntax.Tm_quoted uu____72665 ->
            let uu____72672 = infer env e  in return_if uu____72672
        | FStar_Syntax_Syntax.Tm_app uu____72679 ->
            let uu____72696 = infer env e  in return_if uu____72696
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____72704 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____72704 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____72769) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____72775) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____72781,uu____72782) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____72823 ->
            let uu____72837 =
              let uu____72839 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____72839  in
            failwith uu____72837
        | FStar_Syntax_Syntax.Tm_type uu____72848 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____72856 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____72878 ->
            let uu____72885 =
              let uu____72887 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____72887  in
            failwith uu____72885
        | FStar_Syntax_Syntax.Tm_uvar uu____72896 ->
            let uu____72909 =
              let uu____72911 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____72911  in
            failwith uu____72909
        | FStar_Syntax_Syntax.Tm_delayed uu____72920 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____72950 =
              let uu____72952 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____72952  in
            failwith uu____72950

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
      let uu____72982 =
        let uu____72983 = FStar_Syntax_Subst.compress e  in
        uu____72983.FStar_Syntax_Syntax.n  in
      match uu____72982 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____73002 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____73002
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____73053;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____73054;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____73060 =
                  let uu___1360_73061 = rc  in
                  let uu____73062 =
                    let uu____73067 =
                      let uu____73070 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____73070  in
                    FStar_Pervasives_Native.Some uu____73067  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_73061.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____73062;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_73061.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____73060
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_73082 = env  in
            let uu____73083 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____73083;
              subst = (uu___1366_73082.subst);
              tc_const = (uu___1366_73082.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____73109  ->
                 match uu____73109 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_73132 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_73132.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_73132.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____73133 =
            FStar_List.fold_left
              (fun uu____73164  ->
                 fun uu____73165  ->
                   match (uu____73164, uu____73165) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____73223 = is_C c  in
                       if uu____73223
                       then
                         let xw =
                           let uu____73233 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____73233
                            in
                         let x =
                           let uu___1385_73236 = bv  in
                           let uu____73237 =
                             let uu____73240 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____73240  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_73236.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_73236.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____73237
                           }  in
                         let env3 =
                           let uu___1388_73242 = env2  in
                           let uu____73243 =
                             let uu____73246 =
                               let uu____73247 =
                                 let uu____73254 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____73254)  in
                               FStar_Syntax_Syntax.NT uu____73247  in
                             uu____73246 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_73242.tcenv);
                             subst = uu____73243;
                             tc_const = (uu___1388_73242.tc_const)
                           }  in
                         let uu____73259 =
                           let uu____73262 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____73263 =
                             let uu____73266 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____73266 :: acc  in
                           uu____73262 :: uu____73263  in
                         (env3, uu____73259)
                       else
                         (let x =
                            let uu___1391_73272 = bv  in
                            let uu____73273 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_73272.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_73272.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____73273
                            }  in
                          let uu____73276 =
                            let uu____73279 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____73279 :: acc  in
                          (env2, uu____73276))) (env1, []) binders1
             in
          (match uu____73133 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____73299 =
                 let check_what =
                   let uu____73325 = is_monadic rc_opt1  in
                   if uu____73325 then check_m else check_n  in
                 let uu____73342 = check_what env2 body1  in
                 match uu____73342 with
                 | (t,s_body,u_body) ->
                     let uu____73362 =
                       let uu____73365 =
                         let uu____73366 = is_monadic rc_opt1  in
                         if uu____73366 then M t else N t  in
                       comp_of_nm uu____73365  in
                     (uu____73362, s_body, u_body)
                  in
               (match uu____73299 with
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
                                 let uu____73406 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_73412  ->
                                           match uu___591_73412 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____73415 -> false))
                                    in
                                 if uu____73406
                                 then
                                   let uu____73418 =
                                     FStar_List.filter
                                       (fun uu___592_73422  ->
                                          match uu___592_73422 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____73425 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____73418
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____73436 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_73442  ->
                                         match uu___593_73442 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____73445 -> false))
                                  in
                               if uu____73436
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_73454  ->
                                        match uu___594_73454 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____73457 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____73459 =
                                   let uu____73460 =
                                     let uu____73465 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____73465
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____73460 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____73459
                               else
                                 (let uu____73472 =
                                    let uu___1432_73473 = rc  in
                                    let uu____73474 =
                                      let uu____73479 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____73479
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_73473.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____73474;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_73473.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____73472))
                       in
                    let uu____73484 =
                      let comp1 =
                        let uu____73492 = is_monadic rc_opt1  in
                        let uu____73494 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____73492 uu____73494
                         in
                      let uu____73495 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____73495,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____73484 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____73533 =
                             let uu____73534 =
                               let uu____73553 =
                                 let uu____73556 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____73556 s_rc_opt  in
                               (s_binders1, s_body1, uu____73553)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73534  in
                           mk1 uu____73533  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____73576 =
                             let uu____73577 =
                               let uu____73596 =
                                 let uu____73599 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____73599 u_rc_opt  in
                               (u_binders2, u_body2, uu____73596)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73577  in
                           mk1 uu____73576  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____73615;_};
            FStar_Syntax_Syntax.fv_delta = uu____73616;
            FStar_Syntax_Syntax.fv_qual = uu____73617;_}
          ->
          let uu____73620 =
            let uu____73625 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____73625  in
          (match uu____73620 with
           | (uu____73656,t) ->
               let uu____73658 =
                 let uu____73659 = normalize1 t  in N uu____73659  in
               (uu____73658, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____73660;
             FStar_Syntax_Syntax.vars = uu____73661;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73740 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73740 with
           | (unary_op1,uu____73764) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____73835;
             FStar_Syntax_Syntax.vars = uu____73836;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73932 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73932 with
           | (unary_op1,uu____73956) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74035;
             FStar_Syntax_Syntax.vars = uu____74036;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____74074 = infer env a  in
          (match uu____74074 with
           | (t,s,u) ->
               let uu____74090 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74090 with
                | (head1,uu____74114) ->
                    let uu____74139 =
                      let uu____74140 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____74140  in
                    let uu____74141 =
                      let uu____74142 =
                        let uu____74143 =
                          let uu____74160 =
                            let uu____74171 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74171]  in
                          (head1, uu____74160)  in
                        FStar_Syntax_Syntax.Tm_app uu____74143  in
                      mk1 uu____74142  in
                    let uu____74208 =
                      let uu____74209 =
                        let uu____74210 =
                          let uu____74227 =
                            let uu____74238 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74238]  in
                          (head1, uu____74227)  in
                        FStar_Syntax_Syntax.Tm_app uu____74210  in
                      mk1 uu____74209  in
                    (uu____74139, uu____74141, uu____74208)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74275;
             FStar_Syntax_Syntax.vars = uu____74276;_},(a1,uu____74278)::a2::[])
          ->
          let uu____74334 = infer env a1  in
          (match uu____74334 with
           | (t,s,u) ->
               let uu____74350 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74350 with
                | (head1,uu____74374) ->
                    let uu____74399 =
                      let uu____74400 =
                        let uu____74401 =
                          let uu____74418 =
                            let uu____74429 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74429; a2]  in
                          (head1, uu____74418)  in
                        FStar_Syntax_Syntax.Tm_app uu____74401  in
                      mk1 uu____74400  in
                    let uu____74474 =
                      let uu____74475 =
                        let uu____74476 =
                          let uu____74493 =
                            let uu____74504 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74504; a2]  in
                          (head1, uu____74493)  in
                        FStar_Syntax_Syntax.Tm_app uu____74476  in
                      mk1 uu____74475  in
                    (t, uu____74399, uu____74474)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74549;
             FStar_Syntax_Syntax.vars = uu____74550;_},uu____74551)
          ->
          let uu____74576 =
            let uu____74582 =
              let uu____74584 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74584
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74582)  in
          FStar_Errors.raise_error uu____74576 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74594;
             FStar_Syntax_Syntax.vars = uu____74595;_},uu____74596)
          ->
          let uu____74621 =
            let uu____74627 =
              let uu____74629 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74629
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74627)  in
          FStar_Errors.raise_error uu____74621 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____74665 = check_n env head1  in
          (match uu____74665 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____74688 =
                   let uu____74689 = FStar_Syntax_Subst.compress t  in
                   uu____74689.FStar_Syntax_Syntax.n  in
                 match uu____74688 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____74693 -> true
                 | uu____74709 -> false  in
               let rec flatten1 t =
                 let uu____74731 =
                   let uu____74732 = FStar_Syntax_Subst.compress t  in
                   uu____74732.FStar_Syntax_Syntax.n  in
                 match uu____74731 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____74751);
                                FStar_Syntax_Syntax.pos = uu____74752;
                                FStar_Syntax_Syntax.vars = uu____74753;_})
                     when is_arrow t1 ->
                     let uu____74782 = flatten1 t1  in
                     (match uu____74782 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____74882,uu____74883) -> flatten1 e1
                 | uu____74924 ->
                     let uu____74925 =
                       let uu____74931 =
                         let uu____74933 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____74933
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____74931)  in
                     FStar_Errors.raise_err uu____74925
                  in
               let uu____74951 = flatten1 t_head  in
               (match uu____74951 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____75026 =
                          let uu____75032 =
                            let uu____75034 = FStar_Util.string_of_int n1  in
                            let uu____75042 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____75054 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____75034 uu____75042 uu____75054
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____75032)
                           in
                        FStar_Errors.raise_err uu____75026)
                     else ();
                     (let uu____75066 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____75066 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____75119 args1 =
                            match uu____75119 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____75219 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____75219
                                 | (binders3,[]) ->
                                     let uu____75257 =
                                       let uu____75258 =
                                         let uu____75261 =
                                           let uu____75262 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____75262
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____75261
                                          in
                                       uu____75258.FStar_Syntax_Syntax.n  in
                                     (match uu____75257 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____75295 =
                                            let uu____75296 =
                                              let uu____75297 =
                                                let uu____75312 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____75312)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____75297
                                               in
                                            mk1 uu____75296  in
                                          N uu____75295
                                      | uu____75325 -> failwith "wat?")
                                 | ([],uu____75327::uu____75328) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____75381)::binders3,(arg,uu____75384)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____75471 = FStar_List.splitAt n' binders1
                             in
                          (match uu____75471 with
                           | (binders2,uu____75509) ->
                               let uu____75542 =
                                 let uu____75565 =
                                   FStar_List.map2
                                     (fun uu____75627  ->
                                        fun uu____75628  ->
                                          match (uu____75627, uu____75628)
                                          with
                                          | ((bv,uu____75676),(arg,q)) ->
                                              let uu____75705 =
                                                let uu____75706 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____75706.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____75705 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____75727 ->
                                                   let uu____75728 =
                                                     let uu____75735 =
                                                       star_type' env arg  in
                                                     (uu____75735, q)  in
                                                   (uu____75728, [(arg, q)])
                                               | uu____75772 ->
                                                   let uu____75773 =
                                                     check_n env arg  in
                                                   (match uu____75773 with
                                                    | (uu____75798,s_arg,u_arg)
                                                        ->
                                                        let uu____75801 =
                                                          let uu____75810 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____75810
                                                          then
                                                            let uu____75821 =
                                                              let uu____75828
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____75828,
                                                                q)
                                                               in
                                                            [uu____75821;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____75801))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____75565  in
                               (match uu____75542 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____75956 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____75969 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____75956, uu____75969)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____76038) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____76044) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____76050,uu____76051) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____76093 =
            let uu____76094 = env.tc_const c  in N uu____76094  in
          (uu____76093, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____76101 ->
          let uu____76115 =
            let uu____76117 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____76117  in
          failwith uu____76115
      | FStar_Syntax_Syntax.Tm_type uu____76126 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____76134 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____76156 ->
          let uu____76163 =
            let uu____76165 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____76165  in
          failwith uu____76163
      | FStar_Syntax_Syntax.Tm_uvar uu____76174 ->
          let uu____76187 =
            let uu____76189 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____76189  in
          failwith uu____76187
      | FStar_Syntax_Syntax.Tm_delayed uu____76198 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____76228 =
            let uu____76230 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____76230  in
          failwith uu____76228

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
          let uu____76279 = check_n env e0  in
          match uu____76279 with
          | (uu____76292,s_e0,u_e0) ->
              let uu____76295 =
                let uu____76324 =
                  FStar_List.map
                    (fun b  ->
                       let uu____76385 = FStar_Syntax_Subst.open_branch b  in
                       match uu____76385 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_76427 = env  in
                             let uu____76428 =
                               let uu____76429 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____76429
                                in
                             {
                               tcenv = uu____76428;
                               subst = (uu___1707_76427.subst);
                               tc_const = (uu___1707_76427.tc_const)
                             }  in
                           let uu____76432 = f env1 body  in
                           (match uu____76432 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____76504 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____76324  in
              (match uu____76295 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____76610 = FStar_List.hd nms  in
                     match uu____76610 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_76619  ->
                          match uu___595_76619 with
                          | M uu____76621 -> true
                          | uu____76623 -> false) nms
                      in
                   let uu____76625 =
                     let uu____76662 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____76752  ->
                              match uu____76752 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____76936 =
                                         check env original_body (M t2)  in
                                       (match uu____76936 with
                                        | (uu____76973,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____77012,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____76662  in
                   (match uu____76625 with
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
                              (fun uu____77201  ->
                                 match uu____77201 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____77252 =
                                         let uu____77253 =
                                           let uu____77270 =
                                             let uu____77281 =
                                               let uu____77290 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____77293 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____77290, uu____77293)  in
                                             [uu____77281]  in
                                           (s_body, uu____77270)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____77253
                                          in
                                       mk1 uu____77252  in
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
                            let uu____77428 =
                              let uu____77429 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____77429]  in
                            let uu____77448 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____77428 uu____77448
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____77472 =
                              let uu____77481 =
                                let uu____77488 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____77488
                                 in
                              [uu____77481]  in
                            let uu____77507 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____77472 uu____77507
                             in
                          let uu____77510 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____77549 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____77510, uu____77549)
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
                           let uu____77659 =
                             let uu____77660 =
                               let uu____77661 =
                                 let uu____77688 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____77688,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____77661
                                in
                             mk1 uu____77660  in
                           let uu____77747 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____77659, uu____77747))))

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
              let uu____77812 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____77812]  in
            let uu____77831 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____77831 with
            | (x_binders1,e21) ->
                let uu____77844 = infer env e1  in
                (match uu____77844 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____77861 = is_C t1  in
                       if uu____77861
                       then
                         let uu___1793_77864 = binding  in
                         let uu____77865 =
                           let uu____77868 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____77868  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_77864.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_77864.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____77865;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_77864.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_77864.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_77864.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_77864.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_77872 = env  in
                       let uu____77873 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_77875 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_77875.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_77875.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____77873;
                         subst = (uu___1796_77872.subst);
                         tc_const = (uu___1796_77872.tc_const)
                       }  in
                     let uu____77876 = proceed env1 e21  in
                     (match uu____77876 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_77893 = binding  in
                            let uu____77894 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_77893.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_77893.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____77894;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_77893.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_77893.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_77893.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_77893.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____77897 =
                            let uu____77898 =
                              let uu____77899 =
                                let uu____77913 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_77930 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_77930.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_77930.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_77930.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_77930.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_77930.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_77930.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____77913)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77899  in
                            mk1 uu____77898  in
                          let uu____77931 =
                            let uu____77932 =
                              let uu____77933 =
                                let uu____77947 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_77964 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_77964.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_77964.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_77964.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_77964.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_77964.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_77964.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____77947)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77933  in
                            mk1 uu____77932  in
                          (nm_rec, uu____77897, uu____77931))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_77969 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_77969.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_77969.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_77969.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_77969.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_77969.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_77971 = env  in
                       let uu____77972 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_77974 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_77974.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_77974.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____77972;
                         subst = (uu___1820_77971.subst);
                         tc_const = (uu___1820_77971.tc_const)
                       }  in
                     let uu____77975 = ensure_m env1 e21  in
                     (match uu____77975 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____77999 =
                              let uu____78000 =
                                let uu____78017 =
                                  let uu____78028 =
                                    let uu____78037 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____78040 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78037, uu____78040)  in
                                  [uu____78028]  in
                                (s_e2, uu____78017)  in
                              FStar_Syntax_Syntax.Tm_app uu____78000  in
                            mk1 uu____77999  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____78082 =
                              let uu____78083 =
                                let uu____78100 =
                                  let uu____78111 =
                                    let uu____78120 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____78120)  in
                                  [uu____78111]  in
                                (s_e1, uu____78100)  in
                              FStar_Syntax_Syntax.Tm_app uu____78083  in
                            mk1 uu____78082  in
                          let uu____78156 =
                            let uu____78157 =
                              let uu____78158 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____78158]  in
                            FStar_Syntax_Util.abs uu____78157 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____78177 =
                            let uu____78178 =
                              let uu____78179 =
                                let uu____78193 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_78210 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_78210.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_78210.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_78210.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_78210.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_78210.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_78210.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78193)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78179  in
                            mk1 uu____78178  in
                          ((M t2), uu____78156, uu____78177)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78220 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____78220  in
      let uu____78221 = check env e mn  in
      match uu____78221 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78237 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78260 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____78260  in
      let uu____78261 = check env e mn  in
      match uu____78261 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78277 -> failwith "[check_m]: impossible"

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
        (let uu____78310 =
           let uu____78312 = is_C c  in Prims.op_Negation uu____78312  in
         if uu____78310 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____78326 =
           let uu____78327 = FStar_Syntax_Subst.compress c  in
           uu____78327.FStar_Syntax_Syntax.n  in
         match uu____78326 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____78356 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____78356 with
              | (wp_head,wp_args) ->
                  ((let uu____78400 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____78419 =
                           let uu____78421 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____78421
                            in
                         Prims.op_Negation uu____78419)
                       in
                    if uu____78400 then failwith "mismatch" else ());
                   (let uu____78434 =
                      let uu____78435 =
                        let uu____78452 =
                          FStar_List.map2
                            (fun uu____78490  ->
                               fun uu____78491  ->
                                 match (uu____78490, uu____78491) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____78553 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____78553
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____78562 =
                                         let uu____78564 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____78564 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____78562
                                       then
                                         let uu____78566 =
                                           let uu____78572 =
                                             let uu____78574 =
                                               print_implicit q  in
                                             let uu____78576 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____78574 uu____78576
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____78572)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____78566
                                       else ());
                                      (let uu____78582 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____78582, q)))) args wp_args
                           in
                        (head1, uu____78452)  in
                      FStar_Syntax_Syntax.Tm_app uu____78435  in
                    mk1 uu____78434)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____78628 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____78628 with
              | (binders_orig,comp1) ->
                  let uu____78635 =
                    let uu____78652 =
                      FStar_List.map
                        (fun uu____78692  ->
                           match uu____78692 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____78720 = is_C h  in
                               if uu____78720
                               then
                                 let w' =
                                   let uu____78736 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____78736
                                    in
                                 let uu____78738 =
                                   let uu____78747 =
                                     let uu____78756 =
                                       let uu____78763 =
                                         let uu____78764 =
                                           let uu____78765 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____78765  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____78764
                                          in
                                       (uu____78763, q)  in
                                     [uu____78756]  in
                                   (w', q) :: uu____78747  in
                                 (w', uu____78738)
                               else
                                 (let x =
                                    let uu____78799 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____78799
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____78652  in
                  (match uu____78635 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____78873 =
                           let uu____78876 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____78876
                            in
                         FStar_Syntax_Subst.subst_comp uu____78873 comp1  in
                       let app =
                         let uu____78880 =
                           let uu____78881 =
                             let uu____78898 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____78917 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____78918 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78917, uu____78918)) bvs
                                in
                             (wp, uu____78898)  in
                           FStar_Syntax_Syntax.Tm_app uu____78881  in
                         mk1 uu____78880  in
                       let comp3 =
                         let uu____78933 = type_of_comp comp2  in
                         let uu____78934 = is_monadic_comp comp2  in
                         trans_G env uu____78933 uu____78934 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____78937,uu____78938) ->
             trans_F_ env e wp
         | uu____78979 -> failwith "impossible trans_F_")

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
            let uu____78987 =
              let uu____78988 = star_type' env h  in
              let uu____78991 =
                let uu____79002 =
                  let uu____79011 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____79011)  in
                [uu____79002]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____78988;
                FStar_Syntax_Syntax.effect_args = uu____78991;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____78987
          else
            (let uu____79037 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____79037)

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
    fun t  -> let uu____79058 = n env.tcenv t  in star_type' env uu____79058
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____79078 = n env.tcenv t  in check_n env uu____79078
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____79095 = n env.tcenv c  in
        let uu____79096 = n env.tcenv wp  in
        trans_F_ env uu____79095 uu____79096
  