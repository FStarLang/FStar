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
              let uu___613_65898 = a  in
              let uu____65899 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_65898.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_65898.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____65899
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____65912 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____65912
             then
               (d "Elaborating extra WP combinators";
                (let uu____65918 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____65918))
             else ());
            (let rec collect_binders t =
               let uu____65937 =
                 let uu____65938 =
                   let uu____65941 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____65941
                    in
                 uu____65938.FStar_Syntax_Syntax.n  in
               match uu____65937 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____65976) -> t1
                     | uu____65985 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____65987 = collect_binders rest  in
                   FStar_List.append bs uu____65987
               | FStar_Syntax_Syntax.Tm_type uu____66002 -> []
               | uu____66009 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____66036 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____66036
                 FStar_Syntax_Util.name_binders
                in
             (let uu____66062 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____66062
              then
                let uu____66066 =
                  let uu____66068 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____66068  in
                d uu____66066
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____66106 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____66106 with
                | (sigelt,fv) ->
                    ((let uu____66114 =
                        let uu____66117 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____66117
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____66114);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____66241  ->
                     match uu____66241 with
                     | (t,b) ->
                         let uu____66255 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____66255))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____66294 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____66294))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____66328 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____66328)
                 in
              let uu____66331 =
                let uu____66348 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____66373 =
                        let uu____66376 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____66376  in
                      FStar_Syntax_Util.arrow gamma uu____66373  in
                    let uu____66377 =
                      let uu____66378 =
                        let uu____66387 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____66394 =
                          let uu____66403 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____66403]  in
                        uu____66387 :: uu____66394  in
                      FStar_List.append binders uu____66378  in
                    FStar_Syntax_Util.abs uu____66377 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____66434 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____66435 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____66434, uu____66435)  in
                match uu____66348 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____66477 =
                        let uu____66478 =
                          let uu____66495 =
                            let uu____66506 =
                              FStar_List.map
                                (fun uu____66528  ->
                                   match uu____66528 with
                                   | (bv,uu____66540) ->
                                       let uu____66545 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____66546 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____66545, uu____66546)) binders
                               in
                            let uu____66548 =
                              let uu____66555 =
                                let uu____66560 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____66561 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____66560, uu____66561)  in
                              let uu____66563 =
                                let uu____66570 =
                                  let uu____66575 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____66575)  in
                                [uu____66570]  in
                              uu____66555 :: uu____66563  in
                            FStar_List.append uu____66506 uu____66548  in
                          (fv, uu____66495)  in
                        FStar_Syntax_Syntax.Tm_app uu____66478  in
                      mk1 uu____66477  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____66331 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____66648 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____66648
                       in
                    let ret1 =
                      let uu____66653 =
                        let uu____66654 =
                          let uu____66657 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____66657  in
                        FStar_Syntax_Util.residual_tot uu____66654  in
                      FStar_Pervasives_Native.Some uu____66653  in
                    let body =
                      let uu____66661 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____66661 ret1  in
                    let uu____66664 =
                      let uu____66665 = mk_all_implicit binders  in
                      let uu____66672 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____66665 uu____66672  in
                    FStar_Syntax_Util.abs uu____66664 body ret1  in
                  let c_pure1 =
                    let uu____66710 = mk_lid "pure"  in
                    register env1 uu____66710 c_pure  in
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
                      let uu____66720 =
                        let uu____66721 =
                          let uu____66722 =
                            let uu____66731 =
                              let uu____66738 =
                                let uu____66739 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____66739
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____66738  in
                            [uu____66731]  in
                          let uu____66752 =
                            let uu____66755 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____66755  in
                          FStar_Syntax_Util.arrow uu____66722 uu____66752  in
                        mk_gctx uu____66721  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____66720
                       in
                    let r =
                      let uu____66758 =
                        let uu____66759 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66759  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____66758
                       in
                    let ret1 =
                      let uu____66764 =
                        let uu____66765 =
                          let uu____66768 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66768  in
                        FStar_Syntax_Util.residual_tot uu____66765  in
                      FStar_Pervasives_Native.Some uu____66764  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____66778 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____66781 =
                          let uu____66792 =
                            let uu____66795 =
                              let uu____66796 =
                                let uu____66797 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____66797
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____66796  in
                            [uu____66795]  in
                          FStar_List.append gamma_as_args uu____66792  in
                        FStar_Syntax_Util.mk_app uu____66778 uu____66781  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____66800 =
                      let uu____66801 = mk_all_implicit binders  in
                      let uu____66808 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____66801 uu____66808  in
                    FStar_Syntax_Util.abs uu____66800 outer_body ret1  in
                  let c_app1 =
                    let uu____66860 = mk_lid "app"  in
                    register env1 uu____66860 c_app  in
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
                      let uu____66872 =
                        let uu____66881 =
                          let uu____66888 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____66888  in
                        [uu____66881]  in
                      let uu____66901 =
                        let uu____66904 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____66904  in
                      FStar_Syntax_Util.arrow uu____66872 uu____66901  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____66908 =
                        let uu____66909 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66909  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____66908
                       in
                    let ret1 =
                      let uu____66914 =
                        let uu____66915 =
                          let uu____66918 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66918  in
                        FStar_Syntax_Util.residual_tot uu____66915  in
                      FStar_Pervasives_Native.Some uu____66914  in
                    let uu____66919 =
                      let uu____66920 = mk_all_implicit binders  in
                      let uu____66927 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____66920 uu____66927  in
                    let uu____66978 =
                      let uu____66981 =
                        let uu____66992 =
                          let uu____66995 =
                            let uu____66996 =
                              let uu____67007 =
                                let uu____67010 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____67010]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67007
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____66996  in
                          let uu____67019 =
                            let uu____67022 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____67022]  in
                          uu____66995 :: uu____67019  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____66992
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____66981  in
                    FStar_Syntax_Util.abs uu____66919 uu____66978 ret1  in
                  let c_lift11 =
                    let uu____67032 = mk_lid "lift1"  in
                    register env1 uu____67032 c_lift1  in
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
                      let uu____67046 =
                        let uu____67055 =
                          let uu____67062 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67062  in
                        let uu____67063 =
                          let uu____67072 =
                            let uu____67079 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____67079  in
                          [uu____67072]  in
                        uu____67055 :: uu____67063  in
                      let uu____67098 =
                        let uu____67101 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____67101  in
                      FStar_Syntax_Util.arrow uu____67046 uu____67098  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____67105 =
                        let uu____67106 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____67106  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____67105
                       in
                    let a2 =
                      let uu____67109 =
                        let uu____67110 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____67110  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____67109
                       in
                    let ret1 =
                      let uu____67115 =
                        let uu____67116 =
                          let uu____67119 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____67119  in
                        FStar_Syntax_Util.residual_tot uu____67116  in
                      FStar_Pervasives_Native.Some uu____67115  in
                    let uu____67120 =
                      let uu____67121 = mk_all_implicit binders  in
                      let uu____67128 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____67121 uu____67128  in
                    let uu____67193 =
                      let uu____67196 =
                        let uu____67207 =
                          let uu____67210 =
                            let uu____67211 =
                              let uu____67222 =
                                let uu____67225 =
                                  let uu____67226 =
                                    let uu____67237 =
                                      let uu____67240 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____67240]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____67237
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____67226
                                   in
                                let uu____67249 =
                                  let uu____67252 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____67252]  in
                                uu____67225 :: uu____67249  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67222
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____67211  in
                          let uu____67261 =
                            let uu____67264 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____67264]  in
                          uu____67210 :: uu____67261  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67207
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67196  in
                    FStar_Syntax_Util.abs uu____67120 uu____67193 ret1  in
                  let c_lift21 =
                    let uu____67274 = mk_lid "lift2"  in
                    register env1 uu____67274 c_lift2  in
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
                      let uu____67286 =
                        let uu____67295 =
                          let uu____67302 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67302  in
                        [uu____67295]  in
                      let uu____67315 =
                        let uu____67318 =
                          let uu____67319 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____67319  in
                        FStar_Syntax_Syntax.mk_Total uu____67318  in
                      FStar_Syntax_Util.arrow uu____67286 uu____67315  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____67325 =
                        let uu____67326 =
                          let uu____67329 =
                            let uu____67330 =
                              let uu____67339 =
                                let uu____67346 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____67346
                                 in
                              [uu____67339]  in
                            let uu____67359 =
                              let uu____67362 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____67362  in
                            FStar_Syntax_Util.arrow uu____67330 uu____67359
                             in
                          mk_ctx uu____67329  in
                        FStar_Syntax_Util.residual_tot uu____67326  in
                      FStar_Pervasives_Native.Some uu____67325  in
                    let e1 =
                      let uu____67364 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____67364
                       in
                    let body =
                      let uu____67369 =
                        let uu____67370 =
                          let uu____67379 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____67379]  in
                        FStar_List.append gamma uu____67370  in
                      let uu____67404 =
                        let uu____67407 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____67410 =
                          let uu____67421 =
                            let uu____67422 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____67422  in
                          let uu____67423 = args_of_binders1 gamma  in
                          uu____67421 :: uu____67423  in
                        FStar_Syntax_Util.mk_app uu____67407 uu____67410  in
                      FStar_Syntax_Util.abs uu____67369 uu____67404 ret1  in
                    let uu____67426 =
                      let uu____67427 = mk_all_implicit binders  in
                      let uu____67434 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____67427 uu____67434  in
                    FStar_Syntax_Util.abs uu____67426 body ret1  in
                  let c_push1 =
                    let uu____67479 = mk_lid "push"  in
                    register env1 uu____67479 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____67506 =
                        let uu____67507 =
                          let uu____67524 = args_of_binders1 binders  in
                          (c, uu____67524)  in
                        FStar_Syntax_Syntax.Tm_app uu____67507  in
                      mk1 uu____67506
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____67553 =
                        let uu____67554 =
                          let uu____67563 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____67570 =
                            let uu____67579 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____67579]  in
                          uu____67563 :: uu____67570  in
                        let uu____67604 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____67554 uu____67604  in
                      FStar_Syntax_Syntax.mk_Total uu____67553  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____67609 =
                      let uu____67610 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____67610  in
                    let uu____67625 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____67630 =
                        let uu____67633 =
                          let uu____67644 =
                            let uu____67647 =
                              let uu____67648 =
                                let uu____67659 =
                                  let uu____67668 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____67668  in
                                [uu____67659]  in
                              FStar_Syntax_Util.mk_app l_ite uu____67648  in
                            [uu____67647]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____67644
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____67633  in
                      FStar_Syntax_Util.ascribe uu____67630
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____67609 uu____67625
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____67712 = mk_lid "wp_if_then_else"  in
                    register env1 uu____67712 wp_if_then_else  in
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
                      let uu____67729 =
                        let uu____67740 =
                          let uu____67743 =
                            let uu____67744 =
                              let uu____67755 =
                                let uu____67758 =
                                  let uu____67759 =
                                    let uu____67770 =
                                      let uu____67779 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67779
                                       in
                                    [uu____67770]  in
                                  FStar_Syntax_Util.mk_app l_and uu____67759
                                   in
                                [uu____67758]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67755
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67744  in
                          let uu____67804 =
                            let uu____67807 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67807]  in
                          uu____67743 :: uu____67804  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67740
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67729  in
                    let uu____67816 =
                      let uu____67817 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67817  in
                    FStar_Syntax_Util.abs uu____67816 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____67833 = mk_lid "wp_assert"  in
                    register env1 uu____67833 wp_assert  in
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
                      let uu____67850 =
                        let uu____67861 =
                          let uu____67864 =
                            let uu____67865 =
                              let uu____67876 =
                                let uu____67879 =
                                  let uu____67880 =
                                    let uu____67891 =
                                      let uu____67900 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67900
                                       in
                                    [uu____67891]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____67880
                                   in
                                [uu____67879]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67876
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67865  in
                          let uu____67925 =
                            let uu____67928 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67928]  in
                          uu____67864 :: uu____67925  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67861
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67850  in
                    let uu____67937 =
                      let uu____67938 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67938  in
                    FStar_Syntax_Util.abs uu____67937 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____67954 = mk_lid "wp_assume"  in
                    register env1 uu____67954 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____67967 =
                        let uu____67976 =
                          let uu____67983 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____67983  in
                        [uu____67976]  in
                      let uu____67996 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____67967 uu____67996  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____68004 =
                        let uu____68015 =
                          let uu____68018 =
                            let uu____68019 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____68019  in
                          let uu____68038 =
                            let uu____68041 =
                              let uu____68042 =
                                let uu____68053 =
                                  let uu____68056 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____68056]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____68053
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____68042
                               in
                            [uu____68041]  in
                          uu____68018 :: uu____68038  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____68015
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____68004  in
                    let uu____68073 =
                      let uu____68074 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____68074  in
                    FStar_Syntax_Util.abs uu____68073 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____68090 = mk_lid "wp_close"  in
                    register env1 uu____68090 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____68101 =
                      let uu____68102 =
                        let uu____68103 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____68103
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____68102
                       in
                    FStar_Pervasives_Native.Some uu____68101  in
                  let mk_forall1 x body =
                    let uu____68115 =
                      let uu____68122 =
                        let uu____68123 =
                          let uu____68140 =
                            let uu____68151 =
                              let uu____68160 =
                                let uu____68161 =
                                  let uu____68162 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____68162]  in
                                FStar_Syntax_Util.abs uu____68161 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____68160  in
                            [uu____68151]  in
                          (FStar_Syntax_Util.tforall, uu____68140)  in
                        FStar_Syntax_Syntax.Tm_app uu____68123  in
                      FStar_Syntax_Syntax.mk uu____68122  in
                    uu____68115 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____68223 =
                      let uu____68224 = FStar_Syntax_Subst.compress t  in
                      uu____68224.FStar_Syntax_Syntax.n  in
                    match uu____68223 with
                    | FStar_Syntax_Syntax.Tm_type uu____68228 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68261  ->
                              match uu____68261 with
                              | (b,uu____68270) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____68275 -> true  in
                  let rec is_monotonic t =
                    let uu____68288 =
                      let uu____68289 = FStar_Syntax_Subst.compress t  in
                      uu____68289.FStar_Syntax_Syntax.n  in
                    match uu____68288 with
                    | FStar_Syntax_Syntax.Tm_type uu____68293 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68326  ->
                              match uu____68326 with
                              | (b,uu____68335) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____68340 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____68414 =
                      let uu____68415 = FStar_Syntax_Subst.compress t1  in
                      uu____68415.FStar_Syntax_Syntax.n  in
                    match uu____68414 with
                    | FStar_Syntax_Syntax.Tm_type uu____68420 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____68423);
                                      FStar_Syntax_Syntax.pos = uu____68424;
                                      FStar_Syntax_Syntax.vars = uu____68425;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68469 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68469
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68479 =
                              let uu____68482 =
                                let uu____68493 =
                                  let uu____68502 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68502  in
                                [uu____68493]  in
                              FStar_Syntax_Util.mk_app x uu____68482  in
                            let uu____68519 =
                              let uu____68522 =
                                let uu____68533 =
                                  let uu____68542 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68542  in
                                [uu____68533]  in
                              FStar_Syntax_Util.mk_app y uu____68522  in
                            mk_rel1 b uu____68479 uu____68519  in
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
                             let uu____68566 =
                               let uu____68569 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68572 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68569 uu____68572  in
                             let uu____68575 =
                               let uu____68578 =
                                 let uu____68581 =
                                   let uu____68592 =
                                     let uu____68601 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68601
                                      in
                                   [uu____68592]  in
                                 FStar_Syntax_Util.mk_app x uu____68581  in
                               let uu____68618 =
                                 let uu____68621 =
                                   let uu____68632 =
                                     let uu____68641 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68641
                                      in
                                   [uu____68632]  in
                                 FStar_Syntax_Util.mk_app y uu____68621  in
                               mk_rel1 b uu____68578 uu____68618  in
                             FStar_Syntax_Util.mk_imp uu____68566 uu____68575
                              in
                           let uu____68658 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68658)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____68661);
                                      FStar_Syntax_Syntax.pos = uu____68662;
                                      FStar_Syntax_Syntax.vars = uu____68663;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68707 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68707
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68717 =
                              let uu____68720 =
                                let uu____68731 =
                                  let uu____68740 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68740  in
                                [uu____68731]  in
                              FStar_Syntax_Util.mk_app x uu____68720  in
                            let uu____68757 =
                              let uu____68760 =
                                let uu____68771 =
                                  let uu____68780 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68780  in
                                [uu____68771]  in
                              FStar_Syntax_Util.mk_app y uu____68760  in
                            mk_rel1 b uu____68717 uu____68757  in
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
                             let uu____68804 =
                               let uu____68807 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68810 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68807 uu____68810  in
                             let uu____68813 =
                               let uu____68816 =
                                 let uu____68819 =
                                   let uu____68830 =
                                     let uu____68839 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68839
                                      in
                                   [uu____68830]  in
                                 FStar_Syntax_Util.mk_app x uu____68819  in
                               let uu____68856 =
                                 let uu____68859 =
                                   let uu____68870 =
                                     let uu____68879 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68879
                                      in
                                   [uu____68870]  in
                                 FStar_Syntax_Util.mk_app y uu____68859  in
                               mk_rel1 b uu____68816 uu____68856  in
                             FStar_Syntax_Util.mk_imp uu____68804 uu____68813
                              in
                           let uu____68896 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68896)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_68935 = t1  in
                          let uu____68936 =
                            let uu____68937 =
                              let uu____68952 =
                                let uu____68955 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____68955  in
                              ([binder], uu____68952)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____68937  in
                          {
                            FStar_Syntax_Syntax.n = uu____68936;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_68935.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_68935.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____68978 ->
                        failwith "unhandled arrow"
                    | uu____68996 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____69033 =
                        let uu____69034 = FStar_Syntax_Subst.compress t1  in
                        uu____69034.FStar_Syntax_Syntax.n  in
                      match uu____69033 with
                      | FStar_Syntax_Syntax.Tm_type uu____69037 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____69064 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____69064
                          ->
                          let project i tuple =
                            let projector =
                              let uu____69085 =
                                let uu____69086 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____69086 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____69085
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____69116 =
                            let uu____69127 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____69145  ->
                                     match uu____69145 with
                                     | (t2,q) ->
                                         let uu____69165 = project i x  in
                                         let uu____69168 = project i y  in
                                         mk_stronger t2 uu____69165
                                           uu____69168) args
                               in
                            match uu____69127 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____69116 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____69222);
                                      FStar_Syntax_Syntax.pos = uu____69223;
                                      FStar_Syntax_Syntax.vars = uu____69224;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69268  ->
                                   match uu____69268 with
                                   | (bv,q) ->
                                       let uu____69282 =
                                         let uu____69284 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69284  in
                                       FStar_Syntax_Syntax.gen_bv uu____69282
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69293 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69293) bvs
                             in
                          let body =
                            let uu____69295 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69298 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69295 uu____69298  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____69307);
                                      FStar_Syntax_Syntax.pos = uu____69308;
                                      FStar_Syntax_Syntax.vars = uu____69309;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69353  ->
                                   match uu____69353 with
                                   | (bv,q) ->
                                       let uu____69367 =
                                         let uu____69369 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69369  in
                                       FStar_Syntax_Syntax.gen_bv uu____69367
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69378 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69378) bvs
                             in
                          let body =
                            let uu____69380 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69383 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69380 uu____69383  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____69390 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____69393 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____69396 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____69399 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____69393 uu____69396 uu____69399  in
                    let uu____69402 =
                      let uu____69403 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____69403  in
                    FStar_Syntax_Util.abs uu____69402 body ret_tot_type  in
                  let stronger1 =
                    let uu____69445 = mk_lid "stronger"  in
                    register env1 uu____69445 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69453 = FStar_Util.prefix gamma  in
                    match uu____69453 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____69519 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____69519
                             in
                          let uu____69524 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____69524 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____69534 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____69534  in
                              let guard_free1 =
                                let uu____69546 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____69546  in
                              let pat =
                                let uu____69550 =
                                  let uu____69561 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____69561]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____69550
                                 in
                              let pattern_guarded_body =
                                let uu____69589 =
                                  let uu____69590 =
                                    let uu____69597 =
                                      let uu____69598 =
                                        let uu____69611 =
                                          let uu____69622 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____69622]  in
                                        [uu____69611]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____69598
                                       in
                                    (body, uu____69597)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____69590  in
                                mk1 uu____69589  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____69669 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____69678 =
                            let uu____69681 =
                              let uu____69682 =
                                let uu____69685 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____69688 =
                                  let uu____69699 = args_of_binders1 wp_args
                                     in
                                  let uu____69702 =
                                    let uu____69705 =
                                      let uu____69706 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____69706
                                       in
                                    [uu____69705]  in
                                  FStar_List.append uu____69699 uu____69702
                                   in
                                FStar_Syntax_Util.mk_app uu____69685
                                  uu____69688
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____69682  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____69681
                             in
                          FStar_Syntax_Util.abs gamma uu____69678
                            ret_gtot_type
                           in
                        let uu____69707 =
                          let uu____69708 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____69708  in
                        FStar_Syntax_Util.abs uu____69707 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____69724 = mk_lid "ite_wp"  in
                    register env1 uu____69724 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69732 = FStar_Util.prefix gamma  in
                    match uu____69732 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____69790 =
                            let uu____69791 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____69798 =
                              let uu____69809 =
                                let uu____69818 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____69818  in
                              [uu____69809]  in
                            FStar_Syntax_Util.mk_app uu____69791 uu____69798
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____69790
                           in
                        let uu____69835 =
                          let uu____69836 =
                            let uu____69845 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____69845 gamma  in
                          FStar_List.append binders uu____69836  in
                        FStar_Syntax_Util.abs uu____69835 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____69867 = mk_lid "null_wp"  in
                    register env1 uu____69867 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____69880 =
                        let uu____69891 =
                          let uu____69894 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____69895 =
                            let uu____69898 =
                              let uu____69899 =
                                let uu____69910 =
                                  let uu____69919 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____69919  in
                                [uu____69910]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____69899
                               in
                            let uu____69936 =
                              let uu____69939 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____69939]  in
                            uu____69898 :: uu____69936  in
                          uu____69894 :: uu____69895  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____69891
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____69880  in
                    let uu____69948 =
                      let uu____69949 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____69949  in
                    FStar_Syntax_Util.abs uu____69948 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____69965 = mk_lid "wp_trivial"  in
                    register env1 uu____69965 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____69971 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____69971
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____69983 =
                      let uu____69984 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____69984  in
                    let uu____70032 =
                      let uu___934_70033 = ed  in
                      let uu____70034 =
                        let uu____70035 = c wp_if_then_else2  in
                        ([], uu____70035)  in
                      let uu____70042 =
                        let uu____70043 = c ite_wp2  in ([], uu____70043)  in
                      let uu____70050 =
                        let uu____70051 = c stronger2  in ([], uu____70051)
                         in
                      let uu____70058 =
                        let uu____70059 = c wp_close2  in ([], uu____70059)
                         in
                      let uu____70066 =
                        let uu____70067 = c wp_assert2  in ([], uu____70067)
                         in
                      let uu____70074 =
                        let uu____70075 = c wp_assume2  in ([], uu____70075)
                         in
                      let uu____70082 =
                        let uu____70083 = c null_wp2  in ([], uu____70083)
                         in
                      let uu____70090 =
                        let uu____70091 = c wp_trivial2  in ([], uu____70091)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_70033.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_70033.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_70033.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_70033.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_70033.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_70033.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_70033.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____70034;
                        FStar_Syntax_Syntax.ite_wp = uu____70042;
                        FStar_Syntax_Syntax.stronger = uu____70050;
                        FStar_Syntax_Syntax.close_wp = uu____70058;
                        FStar_Syntax_Syntax.assert_p = uu____70066;
                        FStar_Syntax_Syntax.assume_p = uu____70074;
                        FStar_Syntax_Syntax.null_wp = uu____70082;
                        FStar_Syntax_Syntax.trivial = uu____70090;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_70033.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_70033.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_70033.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_70033.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_70033.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____69983, uu____70032)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_70115 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_70115.subst);
        tc_const = (uu___939_70115.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____70136 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____70156 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____70177) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_70191  ->
                match uu___585_70191 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____70194 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____70196 ->
        let uu____70197 =
          let uu____70203 =
            let uu____70205 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____70205
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____70203)  in
        FStar_Errors.raise_error uu____70197 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_70215  ->
    match uu___586_70215 with
    | N t ->
        let uu____70218 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____70218
    | M t ->
        let uu____70222 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____70222
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____70231,c) -> nm_of_comp c
    | uu____70253 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____70266 = nm_of_comp c  in
    match uu____70266 with | M uu____70268 -> true | N uu____70270 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____70281 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____70297 =
        let uu____70306 =
          let uu____70313 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____70313  in
        [uu____70306]  in
      let uu____70332 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____70297 uu____70332  in
    let uu____70335 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____70335
  
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
        let uu____70377 =
          let uu____70378 =
            let uu____70393 =
              let uu____70402 =
                let uu____70409 =
                  let uu____70410 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____70410  in
                let uu____70411 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____70409, uu____70411)  in
              [uu____70402]  in
            let uu____70429 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____70393, uu____70429)  in
          FStar_Syntax_Syntax.Tm_arrow uu____70378  in
        mk1 uu____70377

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70469) ->
          let binders1 =
            FStar_List.map
              (fun uu____70515  ->
                 match uu____70515 with
                 | (bv,aqual) ->
                     let uu____70534 =
                       let uu___989_70535 = bv  in
                       let uu____70536 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_70535.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_70535.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____70536
                       }  in
                     (uu____70534, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____70541,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____70543);
                              FStar_Syntax_Syntax.pos = uu____70544;
                              FStar_Syntax_Syntax.vars = uu____70545;_})
               ->
               let uu____70574 =
                 let uu____70575 =
                   let uu____70590 =
                     let uu____70593 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____70593  in
                   (binders1, uu____70590)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____70575  in
               mk1 uu____70574
           | uu____70604 ->
               let uu____70605 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____70605 with
                | N hn ->
                    let uu____70607 =
                      let uu____70608 =
                        let uu____70623 =
                          let uu____70626 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____70626  in
                        (binders1, uu____70623)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70608  in
                    mk1 uu____70607
                | M a ->
                    let uu____70638 =
                      let uu____70639 =
                        let uu____70654 =
                          let uu____70663 =
                            let uu____70672 =
                              let uu____70679 =
                                let uu____70680 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____70680  in
                              let uu____70681 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____70679, uu____70681)  in
                            [uu____70672]  in
                          FStar_List.append binders1 uu____70663  in
                        let uu____70705 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____70654, uu____70705)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70639  in
                    mk1 uu____70638))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____70799 = f x  in
                    FStar_Util.string_builder_append strb uu____70799);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____70808 = f x1  in
                         FStar_Util.string_builder_append strb uu____70808))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____70812 =
              let uu____70818 =
                let uu____70820 = FStar_Syntax_Print.term_to_string t2  in
                let uu____70822 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____70820 uu____70822
                 in
              (FStar_Errors.Warning_DependencyFound, uu____70818)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____70812  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____70844 =
              let uu____70845 = FStar_Syntax_Subst.compress ty  in
              uu____70845.FStar_Syntax_Syntax.n  in
            match uu____70844 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____70871 =
                  let uu____70873 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____70873  in
                if uu____70871
                then false
                else
                  (try
                     (fun uu___1038_70890  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____70914 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____70914 s  in
                              let uu____70917 =
                                let uu____70919 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____70919  in
                              if uu____70917
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____70925 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____70925 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____70950  ->
                                          match uu____70950 with
                                          | (bv,uu____70962) ->
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
            | uu____70990 ->
                ((let uu____70992 =
                    let uu____70998 =
                      let uu____71000 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____71000
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____70998)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____70992);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____71016 =
              let uu____71017 = FStar_Syntax_Subst.compress head2  in
              uu____71017.FStar_Syntax_Syntax.n  in
            match uu____71016 with
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
                  (let uu____71023 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____71023)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____71026 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____71026 with
                 | ((uu____71036,ty),uu____71038) ->
                     let uu____71043 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____71043
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____71056 =
                         let uu____71057 = FStar_Syntax_Subst.compress res
                            in
                         uu____71057.FStar_Syntax_Syntax.n  in
                       (match uu____71056 with
                        | FStar_Syntax_Syntax.Tm_app uu____71061 -> true
                        | uu____71079 ->
                            ((let uu____71081 =
                                let uu____71087 =
                                  let uu____71089 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____71089
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____71087)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____71081);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____71097 -> true
            | FStar_Syntax_Syntax.Tm_name uu____71099 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71102) ->
                is_valid_application t2
            | uu____71107 -> false  in
          let uu____71109 = is_valid_application head1  in
          if uu____71109
          then
            let uu____71112 =
              let uu____71113 =
                let uu____71130 =
                  FStar_List.map
                    (fun uu____71159  ->
                       match uu____71159 with
                       | (t2,qual) ->
                           let uu____71184 = star_type' env t2  in
                           (uu____71184, qual)) args
                   in
                (head1, uu____71130)  in
              FStar_Syntax_Syntax.Tm_app uu____71113  in
            mk1 uu____71112
          else
            (let uu____71201 =
               let uu____71207 =
                 let uu____71209 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____71209
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____71207)  in
             FStar_Errors.raise_err uu____71201)
      | FStar_Syntax_Syntax.Tm_bvar uu____71213 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____71214 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____71215 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____71216 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____71244 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____71244 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_71252 = env  in
                 let uu____71253 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____71253;
                   subst = (uu___1110_71252.subst);
                   tc_const = (uu___1110_71252.tc_const)
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
               ((let uu___1125_71280 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_71280.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_71280.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____71287 =
            let uu____71288 =
              let uu____71295 = star_type' env t2  in (uu____71295, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____71288  in
          mk1 uu____71287
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____71347 =
            let uu____71348 =
              let uu____71375 = star_type' env e  in
              let uu____71378 =
                let uu____71395 =
                  let uu____71404 = star_type' env t2  in
                  FStar_Util.Inl uu____71404  in
                (uu____71395, FStar_Pervasives_Native.None)  in
              (uu____71375, uu____71378, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71348  in
          mk1 uu____71347
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____71492 =
            let uu____71493 =
              let uu____71520 = star_type' env e  in
              let uu____71523 =
                let uu____71540 =
                  let uu____71549 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____71549  in
                (uu____71540, FStar_Pervasives_Native.None)  in
              (uu____71520, uu____71523, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71493  in
          mk1 uu____71492
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____71590,(uu____71591,FStar_Pervasives_Native.Some uu____71592),uu____71593)
          ->
          let uu____71642 =
            let uu____71648 =
              let uu____71650 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____71650
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71648)  in
          FStar_Errors.raise_err uu____71642
      | FStar_Syntax_Syntax.Tm_refine uu____71654 ->
          let uu____71661 =
            let uu____71667 =
              let uu____71669 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____71669
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71667)  in
          FStar_Errors.raise_err uu____71661
      | FStar_Syntax_Syntax.Tm_uinst uu____71673 ->
          let uu____71680 =
            let uu____71686 =
              let uu____71688 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____71688
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71686)  in
          FStar_Errors.raise_err uu____71680
      | FStar_Syntax_Syntax.Tm_quoted uu____71692 ->
          let uu____71699 =
            let uu____71705 =
              let uu____71707 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____71707
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71705)  in
          FStar_Errors.raise_err uu____71699
      | FStar_Syntax_Syntax.Tm_constant uu____71711 ->
          let uu____71712 =
            let uu____71718 =
              let uu____71720 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____71720
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71718)  in
          FStar_Errors.raise_err uu____71712
      | FStar_Syntax_Syntax.Tm_match uu____71724 ->
          let uu____71747 =
            let uu____71753 =
              let uu____71755 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____71755
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71753)  in
          FStar_Errors.raise_err uu____71747
      | FStar_Syntax_Syntax.Tm_let uu____71759 ->
          let uu____71773 =
            let uu____71779 =
              let uu____71781 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____71781
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71779)  in
          FStar_Errors.raise_err uu____71773
      | FStar_Syntax_Syntax.Tm_uvar uu____71785 ->
          let uu____71798 =
            let uu____71804 =
              let uu____71806 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____71806
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71804)  in
          FStar_Errors.raise_err uu____71798
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71810 =
            let uu____71816 =
              let uu____71818 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____71818
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71816)  in
          FStar_Errors.raise_err uu____71810
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71823 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____71823
      | FStar_Syntax_Syntax.Tm_delayed uu____71826 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_71858  ->
    match uu___588_71858 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_71869  ->
                match uu___587_71869 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____71872 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____71882 =
      let uu____71883 = FStar_Syntax_Subst.compress t  in
      uu____71883.FStar_Syntax_Syntax.n  in
    match uu____71882 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____71915 =
            let uu____71916 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____71916  in
          is_C uu____71915  in
        if r
        then
          ((let uu____71940 =
              let uu____71942 =
                FStar_List.for_all
                  (fun uu____71953  ->
                     match uu____71953 with | (h,uu____71962) -> is_C h) args
                 in
              Prims.op_Negation uu____71942  in
            if uu____71940 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____71975 =
              let uu____71977 =
                FStar_List.for_all
                  (fun uu____71989  ->
                     match uu____71989 with
                     | (h,uu____71998) ->
                         let uu____72003 = is_C h  in
                         Prims.op_Negation uu____72003) args
                 in
              Prims.op_Negation uu____71977  in
            if uu____71975 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____72032 = nm_of_comp comp  in
        (match uu____72032 with
         | M t1 ->
             ((let uu____72036 = is_C t1  in
               if uu____72036 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____72045) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____72051) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____72057,uu____72058) -> is_C t1
    | uu____72099 -> false
  
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
          let uu____72135 =
            let uu____72136 =
              let uu____72153 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____72156 =
                let uu____72167 =
                  let uu____72176 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____72176)  in
                [uu____72167]  in
              (uu____72153, uu____72156)  in
            FStar_Syntax_Syntax.Tm_app uu____72136  in
          mk1 uu____72135  in
        let uu____72212 =
          let uu____72213 = FStar_Syntax_Syntax.mk_binder p  in [uu____72213]
           in
        FStar_Syntax_Util.abs uu____72212 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_72238  ->
    match uu___589_72238 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____72241 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____72479 =
          match uu____72479 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____72516 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____72519 =
                       let uu____72521 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____72521  in
                     Prims.op_Negation uu____72519)
                   in
                if uu____72516
                then
                  let uu____72523 =
                    let uu____72529 =
                      let uu____72531 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____72533 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____72535 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____72531 uu____72533 uu____72535
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____72529)  in
                  FStar_Errors.raise_err uu____72523
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____72560 = mk_return env t1 s_e  in
                     ((M t1), uu____72560, u_e)))
               | (M t1,N t2) ->
                   let uu____72567 =
                     let uu____72573 =
                       let uu____72575 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____72577 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____72579 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____72575 uu____72577 uu____72579
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____72573)
                      in
                   FStar_Errors.raise_err uu____72567)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_72631 =
            match uu___590_72631 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____72647 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____72668 =
                let uu____72674 =
                  let uu____72676 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____72676
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____72674)  in
              FStar_Errors.raise_error uu____72668 e2.FStar_Syntax_Syntax.pos
          | M uu____72686 ->
              let uu____72687 = check env1 e2 context_nm  in
              strip_m uu____72687
           in
        let uu____72694 =
          let uu____72695 = FStar_Syntax_Subst.compress e  in
          uu____72695.FStar_Syntax_Syntax.n  in
        match uu____72694 with
        | FStar_Syntax_Syntax.Tm_bvar uu____72704 ->
            let uu____72705 = infer env e  in return_if uu____72705
        | FStar_Syntax_Syntax.Tm_name uu____72712 ->
            let uu____72713 = infer env e  in return_if uu____72713
        | FStar_Syntax_Syntax.Tm_fvar uu____72720 ->
            let uu____72721 = infer env e  in return_if uu____72721
        | FStar_Syntax_Syntax.Tm_abs uu____72728 ->
            let uu____72747 = infer env e  in return_if uu____72747
        | FStar_Syntax_Syntax.Tm_constant uu____72754 ->
            let uu____72755 = infer env e  in return_if uu____72755
        | FStar_Syntax_Syntax.Tm_quoted uu____72762 ->
            let uu____72769 = infer env e  in return_if uu____72769
        | FStar_Syntax_Syntax.Tm_app uu____72776 ->
            let uu____72793 = infer env e  in return_if uu____72793
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____72801 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____72801 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____72866) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____72872) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____72878,uu____72879) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____72920 ->
            let uu____72934 =
              let uu____72936 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____72936  in
            failwith uu____72934
        | FStar_Syntax_Syntax.Tm_type uu____72945 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____72953 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____72975 ->
            let uu____72982 =
              let uu____72984 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____72984  in
            failwith uu____72982
        | FStar_Syntax_Syntax.Tm_uvar uu____72993 ->
            let uu____73006 =
              let uu____73008 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____73008  in
            failwith uu____73006
        | FStar_Syntax_Syntax.Tm_delayed uu____73017 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____73047 =
              let uu____73049 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____73049  in
            failwith uu____73047

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
      let uu____73079 =
        let uu____73080 = FStar_Syntax_Subst.compress e  in
        uu____73080.FStar_Syntax_Syntax.n  in
      match uu____73079 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____73099 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____73099
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____73150;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____73151;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____73157 =
                  let uu___1360_73158 = rc  in
                  let uu____73159 =
                    let uu____73164 =
                      let uu____73167 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____73167  in
                    FStar_Pervasives_Native.Some uu____73164  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_73158.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____73159;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_73158.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____73157
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_73179 = env  in
            let uu____73180 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____73180;
              subst = (uu___1366_73179.subst);
              tc_const = (uu___1366_73179.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____73206  ->
                 match uu____73206 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_73229 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_73229.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_73229.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____73230 =
            FStar_List.fold_left
              (fun uu____73261  ->
                 fun uu____73262  ->
                   match (uu____73261, uu____73262) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____73320 = is_C c  in
                       if uu____73320
                       then
                         let xw =
                           let uu____73330 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____73330
                            in
                         let x =
                           let uu___1385_73333 = bv  in
                           let uu____73334 =
                             let uu____73337 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____73337  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_73333.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_73333.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____73334
                           }  in
                         let env3 =
                           let uu___1388_73339 = env2  in
                           let uu____73340 =
                             let uu____73343 =
                               let uu____73344 =
                                 let uu____73351 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____73351)  in
                               FStar_Syntax_Syntax.NT uu____73344  in
                             uu____73343 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_73339.tcenv);
                             subst = uu____73340;
                             tc_const = (uu___1388_73339.tc_const)
                           }  in
                         let uu____73356 =
                           let uu____73359 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____73360 =
                             let uu____73363 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____73363 :: acc  in
                           uu____73359 :: uu____73360  in
                         (env3, uu____73356)
                       else
                         (let x =
                            let uu___1391_73369 = bv  in
                            let uu____73370 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_73369.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_73369.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____73370
                            }  in
                          let uu____73373 =
                            let uu____73376 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____73376 :: acc  in
                          (env2, uu____73373))) (env1, []) binders1
             in
          (match uu____73230 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____73396 =
                 let check_what =
                   let uu____73422 = is_monadic rc_opt1  in
                   if uu____73422 then check_m else check_n  in
                 let uu____73439 = check_what env2 body1  in
                 match uu____73439 with
                 | (t,s_body,u_body) ->
                     let uu____73459 =
                       let uu____73462 =
                         let uu____73463 = is_monadic rc_opt1  in
                         if uu____73463 then M t else N t  in
                       comp_of_nm uu____73462  in
                     (uu____73459, s_body, u_body)
                  in
               (match uu____73396 with
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
                                 let uu____73503 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_73509  ->
                                           match uu___591_73509 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____73512 -> false))
                                    in
                                 if uu____73503
                                 then
                                   let uu____73515 =
                                     FStar_List.filter
                                       (fun uu___592_73519  ->
                                          match uu___592_73519 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____73522 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____73515
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____73533 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_73539  ->
                                         match uu___593_73539 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____73542 -> false))
                                  in
                               if uu____73533
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_73551  ->
                                        match uu___594_73551 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____73554 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____73556 =
                                   let uu____73557 =
                                     let uu____73562 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____73562
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____73557 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____73556
                               else
                                 (let uu____73569 =
                                    let uu___1432_73570 = rc  in
                                    let uu____73571 =
                                      let uu____73576 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____73576
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_73570.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____73571;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_73570.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____73569))
                       in
                    let uu____73581 =
                      let comp1 =
                        let uu____73589 = is_monadic rc_opt1  in
                        let uu____73591 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____73589 uu____73591
                         in
                      let uu____73592 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____73592,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____73581 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____73630 =
                             let uu____73631 =
                               let uu____73650 =
                                 let uu____73653 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____73653 s_rc_opt  in
                               (s_binders1, s_body1, uu____73650)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73631  in
                           mk1 uu____73630  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____73673 =
                             let uu____73674 =
                               let uu____73693 =
                                 let uu____73696 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____73696 u_rc_opt  in
                               (u_binders2, u_body2, uu____73693)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73674  in
                           mk1 uu____73673  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____73712;_};
            FStar_Syntax_Syntax.fv_delta = uu____73713;
            FStar_Syntax_Syntax.fv_qual = uu____73714;_}
          ->
          let uu____73717 =
            let uu____73722 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____73722  in
          (match uu____73717 with
           | (uu____73753,t) ->
               let uu____73755 =
                 let uu____73756 = normalize1 t  in N uu____73756  in
               (uu____73755, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____73757;
             FStar_Syntax_Syntax.vars = uu____73758;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73837 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73837 with
           | (unary_op1,uu____73861) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____73932;
             FStar_Syntax_Syntax.vars = uu____73933;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____74029 = FStar_Syntax_Util.head_and_args e  in
          (match uu____74029 with
           | (unary_op1,uu____74053) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74132;
             FStar_Syntax_Syntax.vars = uu____74133;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____74171 = infer env a  in
          (match uu____74171 with
           | (t,s,u) ->
               let uu____74187 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74187 with
                | (head1,uu____74211) ->
                    let uu____74236 =
                      let uu____74237 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____74237  in
                    let uu____74238 =
                      let uu____74239 =
                        let uu____74240 =
                          let uu____74257 =
                            let uu____74268 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74268]  in
                          (head1, uu____74257)  in
                        FStar_Syntax_Syntax.Tm_app uu____74240  in
                      mk1 uu____74239  in
                    let uu____74305 =
                      let uu____74306 =
                        let uu____74307 =
                          let uu____74324 =
                            let uu____74335 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74335]  in
                          (head1, uu____74324)  in
                        FStar_Syntax_Syntax.Tm_app uu____74307  in
                      mk1 uu____74306  in
                    (uu____74236, uu____74238, uu____74305)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74372;
             FStar_Syntax_Syntax.vars = uu____74373;_},(a1,uu____74375)::a2::[])
          ->
          let uu____74431 = infer env a1  in
          (match uu____74431 with
           | (t,s,u) ->
               let uu____74447 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74447 with
                | (head1,uu____74471) ->
                    let uu____74496 =
                      let uu____74497 =
                        let uu____74498 =
                          let uu____74515 =
                            let uu____74526 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74526; a2]  in
                          (head1, uu____74515)  in
                        FStar_Syntax_Syntax.Tm_app uu____74498  in
                      mk1 uu____74497  in
                    let uu____74571 =
                      let uu____74572 =
                        let uu____74573 =
                          let uu____74590 =
                            let uu____74601 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74601; a2]  in
                          (head1, uu____74590)  in
                        FStar_Syntax_Syntax.Tm_app uu____74573  in
                      mk1 uu____74572  in
                    (t, uu____74496, uu____74571)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74646;
             FStar_Syntax_Syntax.vars = uu____74647;_},uu____74648)
          ->
          let uu____74673 =
            let uu____74679 =
              let uu____74681 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74681
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74679)  in
          FStar_Errors.raise_error uu____74673 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74691;
             FStar_Syntax_Syntax.vars = uu____74692;_},uu____74693)
          ->
          let uu____74718 =
            let uu____74724 =
              let uu____74726 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74726
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74724)  in
          FStar_Errors.raise_error uu____74718 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____74762 = check_n env head1  in
          (match uu____74762 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____74785 =
                   let uu____74786 = FStar_Syntax_Subst.compress t  in
                   uu____74786.FStar_Syntax_Syntax.n  in
                 match uu____74785 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____74790 -> true
                 | uu____74806 -> false  in
               let rec flatten1 t =
                 let uu____74828 =
                   let uu____74829 = FStar_Syntax_Subst.compress t  in
                   uu____74829.FStar_Syntax_Syntax.n  in
                 match uu____74828 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____74848);
                                FStar_Syntax_Syntax.pos = uu____74849;
                                FStar_Syntax_Syntax.vars = uu____74850;_})
                     when is_arrow t1 ->
                     let uu____74879 = flatten1 t1  in
                     (match uu____74879 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____74979,uu____74980) -> flatten1 e1
                 | uu____75021 ->
                     let uu____75022 =
                       let uu____75028 =
                         let uu____75030 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____75030
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____75028)  in
                     FStar_Errors.raise_err uu____75022
                  in
               let uu____75048 = flatten1 t_head  in
               (match uu____75048 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____75123 =
                          let uu____75129 =
                            let uu____75131 = FStar_Util.string_of_int n1  in
                            let uu____75139 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____75151 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____75131 uu____75139 uu____75151
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____75129)
                           in
                        FStar_Errors.raise_err uu____75123)
                     else ();
                     (let uu____75163 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____75163 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____75216 args1 =
                            match uu____75216 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____75316 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____75316
                                 | (binders3,[]) ->
                                     let uu____75354 =
                                       let uu____75355 =
                                         let uu____75358 =
                                           let uu____75359 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____75359
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____75358
                                          in
                                       uu____75355.FStar_Syntax_Syntax.n  in
                                     (match uu____75354 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____75392 =
                                            let uu____75393 =
                                              let uu____75394 =
                                                let uu____75409 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____75409)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____75394
                                               in
                                            mk1 uu____75393  in
                                          N uu____75392
                                      | uu____75422 -> failwith "wat?")
                                 | ([],uu____75424::uu____75425) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____75478)::binders3,(arg,uu____75481)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____75568 = FStar_List.splitAt n' binders1
                             in
                          (match uu____75568 with
                           | (binders2,uu____75606) ->
                               let uu____75639 =
                                 let uu____75662 =
                                   FStar_List.map2
                                     (fun uu____75724  ->
                                        fun uu____75725  ->
                                          match (uu____75724, uu____75725)
                                          with
                                          | ((bv,uu____75773),(arg,q)) ->
                                              let uu____75802 =
                                                let uu____75803 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____75803.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____75802 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____75824 ->
                                                   let uu____75825 =
                                                     let uu____75832 =
                                                       star_type' env arg  in
                                                     (uu____75832, q)  in
                                                   (uu____75825, [(arg, q)])
                                               | uu____75869 ->
                                                   let uu____75870 =
                                                     check_n env arg  in
                                                   (match uu____75870 with
                                                    | (uu____75895,s_arg,u_arg)
                                                        ->
                                                        let uu____75898 =
                                                          let uu____75907 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____75907
                                                          then
                                                            let uu____75918 =
                                                              let uu____75925
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____75925,
                                                                q)
                                                               in
                                                            [uu____75918;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____75898))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____75662  in
                               (match uu____75639 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____76053 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____76066 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____76053, uu____76066)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____76135) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____76141) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____76147,uu____76148) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____76190 =
            let uu____76191 = env.tc_const c  in N uu____76191  in
          (uu____76190, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____76198 ->
          let uu____76212 =
            let uu____76214 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____76214  in
          failwith uu____76212
      | FStar_Syntax_Syntax.Tm_type uu____76223 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____76231 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____76253 ->
          let uu____76260 =
            let uu____76262 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____76262  in
          failwith uu____76260
      | FStar_Syntax_Syntax.Tm_uvar uu____76271 ->
          let uu____76284 =
            let uu____76286 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____76286  in
          failwith uu____76284
      | FStar_Syntax_Syntax.Tm_delayed uu____76295 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____76325 =
            let uu____76327 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____76327  in
          failwith uu____76325

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
          let uu____76376 = check_n env e0  in
          match uu____76376 with
          | (uu____76389,s_e0,u_e0) ->
              let uu____76392 =
                let uu____76421 =
                  FStar_List.map
                    (fun b  ->
                       let uu____76482 = FStar_Syntax_Subst.open_branch b  in
                       match uu____76482 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_76524 = env  in
                             let uu____76525 =
                               let uu____76526 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____76526
                                in
                             {
                               tcenv = uu____76525;
                               subst = (uu___1707_76524.subst);
                               tc_const = (uu___1707_76524.tc_const)
                             }  in
                           let uu____76529 = f env1 body  in
                           (match uu____76529 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____76601 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____76421  in
              (match uu____76392 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____76707 = FStar_List.hd nms  in
                     match uu____76707 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_76716  ->
                          match uu___595_76716 with
                          | M uu____76718 -> true
                          | uu____76720 -> false) nms
                      in
                   let uu____76722 =
                     let uu____76759 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____76849  ->
                              match uu____76849 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____77033 =
                                         check env original_body (M t2)  in
                                       (match uu____77033 with
                                        | (uu____77070,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____77109,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____76759  in
                   (match uu____76722 with
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
                              (fun uu____77298  ->
                                 match uu____77298 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____77349 =
                                         let uu____77350 =
                                           let uu____77367 =
                                             let uu____77378 =
                                               let uu____77387 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____77390 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____77387, uu____77390)  in
                                             [uu____77378]  in
                                           (s_body, uu____77367)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____77350
                                          in
                                       mk1 uu____77349  in
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
                            let uu____77525 =
                              let uu____77526 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____77526]  in
                            let uu____77545 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____77525 uu____77545
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____77569 =
                              let uu____77578 =
                                let uu____77585 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____77585
                                 in
                              [uu____77578]  in
                            let uu____77604 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____77569 uu____77604
                             in
                          let uu____77607 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____77646 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____77607, uu____77646)
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
                           let uu____77756 =
                             let uu____77757 =
                               let uu____77758 =
                                 let uu____77785 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____77785,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____77758
                                in
                             mk1 uu____77757  in
                           let uu____77844 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____77756, uu____77844))))

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
              let uu____77909 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____77909]  in
            let uu____77928 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____77928 with
            | (x_binders1,e21) ->
                let uu____77941 = infer env e1  in
                (match uu____77941 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____77958 = is_C t1  in
                       if uu____77958
                       then
                         let uu___1793_77961 = binding  in
                         let uu____77962 =
                           let uu____77965 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____77965  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_77961.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_77961.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____77962;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_77961.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_77961.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_77961.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_77961.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_77969 = env  in
                       let uu____77970 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_77972 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_77972.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_77972.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____77970;
                         subst = (uu___1796_77969.subst);
                         tc_const = (uu___1796_77969.tc_const)
                       }  in
                     let uu____77973 = proceed env1 e21  in
                     (match uu____77973 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_77990 = binding  in
                            let uu____77991 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_77990.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_77990.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____77991;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_77990.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_77990.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_77990.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_77990.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____77994 =
                            let uu____77995 =
                              let uu____77996 =
                                let uu____78010 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_78027 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_78027.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_78027.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_78027.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_78027.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_78027.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_78027.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78010)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77996  in
                            mk1 uu____77995  in
                          let uu____78028 =
                            let uu____78029 =
                              let uu____78030 =
                                let uu____78044 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_78061 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_78061.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_78061.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_78061.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_78061.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_78061.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_78061.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78044)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78030  in
                            mk1 uu____78029  in
                          (nm_rec, uu____77994, uu____78028))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_78066 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_78066.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_78066.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_78066.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_78066.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_78066.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_78068 = env  in
                       let uu____78069 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_78071 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_78071.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_78071.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____78069;
                         subst = (uu___1820_78068.subst);
                         tc_const = (uu___1820_78068.tc_const)
                       }  in
                     let uu____78072 = ensure_m env1 e21  in
                     (match uu____78072 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____78096 =
                              let uu____78097 =
                                let uu____78114 =
                                  let uu____78125 =
                                    let uu____78134 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____78137 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78134, uu____78137)  in
                                  [uu____78125]  in
                                (s_e2, uu____78114)  in
                              FStar_Syntax_Syntax.Tm_app uu____78097  in
                            mk1 uu____78096  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____78179 =
                              let uu____78180 =
                                let uu____78197 =
                                  let uu____78208 =
                                    let uu____78217 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____78217)  in
                                  [uu____78208]  in
                                (s_e1, uu____78197)  in
                              FStar_Syntax_Syntax.Tm_app uu____78180  in
                            mk1 uu____78179  in
                          let uu____78253 =
                            let uu____78254 =
                              let uu____78255 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____78255]  in
                            FStar_Syntax_Util.abs uu____78254 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____78274 =
                            let uu____78275 =
                              let uu____78276 =
                                let uu____78290 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_78307 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_78307.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_78307.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_78307.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_78307.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_78307.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_78307.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78290)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78276  in
                            mk1 uu____78275  in
                          ((M t2), uu____78253, uu____78274)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78317 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____78317  in
      let uu____78318 = check env e mn  in
      match uu____78318 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78334 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78357 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____78357  in
      let uu____78358 = check env e mn  in
      match uu____78358 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78374 -> failwith "[check_m]: impossible"

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
        (let uu____78407 =
           let uu____78409 = is_C c  in Prims.op_Negation uu____78409  in
         if uu____78407 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____78423 =
           let uu____78424 = FStar_Syntax_Subst.compress c  in
           uu____78424.FStar_Syntax_Syntax.n  in
         match uu____78423 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____78453 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____78453 with
              | (wp_head,wp_args) ->
                  ((let uu____78497 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____78516 =
                           let uu____78518 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____78518
                            in
                         Prims.op_Negation uu____78516)
                       in
                    if uu____78497 then failwith "mismatch" else ());
                   (let uu____78531 =
                      let uu____78532 =
                        let uu____78549 =
                          FStar_List.map2
                            (fun uu____78587  ->
                               fun uu____78588  ->
                                 match (uu____78587, uu____78588) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____78650 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____78650
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____78659 =
                                         let uu____78661 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____78661 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____78659
                                       then
                                         let uu____78663 =
                                           let uu____78669 =
                                             let uu____78671 =
                                               print_implicit q  in
                                             let uu____78673 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____78671 uu____78673
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____78669)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____78663
                                       else ());
                                      (let uu____78679 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____78679, q)))) args wp_args
                           in
                        (head1, uu____78549)  in
                      FStar_Syntax_Syntax.Tm_app uu____78532  in
                    mk1 uu____78531)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____78725 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____78725 with
              | (binders_orig,comp1) ->
                  let uu____78732 =
                    let uu____78749 =
                      FStar_List.map
                        (fun uu____78789  ->
                           match uu____78789 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____78817 = is_C h  in
                               if uu____78817
                               then
                                 let w' =
                                   let uu____78833 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____78833
                                    in
                                 let uu____78835 =
                                   let uu____78844 =
                                     let uu____78853 =
                                       let uu____78860 =
                                         let uu____78861 =
                                           let uu____78862 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____78862  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____78861
                                          in
                                       (uu____78860, q)  in
                                     [uu____78853]  in
                                   (w', q) :: uu____78844  in
                                 (w', uu____78835)
                               else
                                 (let x =
                                    let uu____78896 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____78896
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____78749  in
                  (match uu____78732 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____78970 =
                           let uu____78973 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____78973
                            in
                         FStar_Syntax_Subst.subst_comp uu____78970 comp1  in
                       let app =
                         let uu____78977 =
                           let uu____78978 =
                             let uu____78995 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____79014 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____79015 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____79014, uu____79015)) bvs
                                in
                             (wp, uu____78995)  in
                           FStar_Syntax_Syntax.Tm_app uu____78978  in
                         mk1 uu____78977  in
                       let comp3 =
                         let uu____79030 = type_of_comp comp2  in
                         let uu____79031 = is_monadic_comp comp2  in
                         trans_G env uu____79030 uu____79031 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____79034,uu____79035) ->
             trans_F_ env e wp
         | uu____79076 -> failwith "impossible trans_F_")

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
            let uu____79084 =
              let uu____79085 = star_type' env h  in
              let uu____79088 =
                let uu____79099 =
                  let uu____79108 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____79108)  in
                [uu____79099]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____79085;
                FStar_Syntax_Syntax.effect_args = uu____79088;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____79084
          else
            (let uu____79134 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____79134)

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
    fun t  -> let uu____79155 = n env.tcenv t  in star_type' env uu____79155
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____79175 = n env.tcenv t  in check_n env uu____79175
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____79192 = n env.tcenv c  in
        let uu____79193 = n env.tcenv wp  in
        trans_F_ env uu____79192 uu____79193
  