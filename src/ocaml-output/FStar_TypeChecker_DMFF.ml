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
              let uu___613_65870 = a  in
              let uu____65871 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_65870.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_65870.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____65871
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____65884 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____65884
             then
               (d "Elaborating extra WP combinators";
                (let uu____65890 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____65890))
             else ());
            (let rec collect_binders t =
               let uu____65909 =
                 let uu____65910 =
                   let uu____65913 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____65913
                    in
                 uu____65910.FStar_Syntax_Syntax.n  in
               match uu____65909 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____65948) -> t1
                     | uu____65957 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____65959 = collect_binders rest  in
                   FStar_List.append bs uu____65959
               | FStar_Syntax_Syntax.Tm_type uu____65974 -> []
               | uu____65981 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____66008 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____66008
                 FStar_Syntax_Util.name_binders
                in
             (let uu____66034 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____66034
              then
                let uu____66038 =
                  let uu____66040 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____66040  in
                d uu____66038
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____66078 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____66078 with
                | (sigelt,fv) ->
                    ((let uu____66086 =
                        let uu____66089 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____66089
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____66086);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____66213  ->
                     match uu____66213 with
                     | (t,b) ->
                         let uu____66227 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____66227))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____66266 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____66266))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____66300 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____66300)
                 in
              let uu____66303 =
                let uu____66320 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____66345 =
                        let uu____66348 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____66348  in
                      FStar_Syntax_Util.arrow gamma uu____66345  in
                    let uu____66349 =
                      let uu____66350 =
                        let uu____66359 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____66366 =
                          let uu____66375 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____66375]  in
                        uu____66359 :: uu____66366  in
                      FStar_List.append binders uu____66350  in
                    FStar_Syntax_Util.abs uu____66349 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____66406 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____66407 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____66406, uu____66407)  in
                match uu____66320 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____66449 =
                        let uu____66450 =
                          let uu____66467 =
                            let uu____66478 =
                              FStar_List.map
                                (fun uu____66500  ->
                                   match uu____66500 with
                                   | (bv,uu____66512) ->
                                       let uu____66517 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____66518 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____66517, uu____66518)) binders
                               in
                            let uu____66520 =
                              let uu____66527 =
                                let uu____66532 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____66533 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____66532, uu____66533)  in
                              let uu____66535 =
                                let uu____66542 =
                                  let uu____66547 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____66547)  in
                                [uu____66542]  in
                              uu____66527 :: uu____66535  in
                            FStar_List.append uu____66478 uu____66520  in
                          (fv, uu____66467)  in
                        FStar_Syntax_Syntax.Tm_app uu____66450  in
                      mk1 uu____66449  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____66303 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____66620 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____66620
                       in
                    let ret1 =
                      let uu____66625 =
                        let uu____66626 =
                          let uu____66629 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____66629  in
                        FStar_Syntax_Util.residual_tot uu____66626  in
                      FStar_Pervasives_Native.Some uu____66625  in
                    let body =
                      let uu____66633 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____66633 ret1  in
                    let uu____66636 =
                      let uu____66637 = mk_all_implicit binders  in
                      let uu____66644 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____66637 uu____66644  in
                    FStar_Syntax_Util.abs uu____66636 body ret1  in
                  let c_pure1 =
                    let uu____66682 = mk_lid "pure"  in
                    register env1 uu____66682 c_pure  in
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
                      let uu____66692 =
                        let uu____66693 =
                          let uu____66694 =
                            let uu____66703 =
                              let uu____66710 =
                                let uu____66711 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____66711
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____66710  in
                            [uu____66703]  in
                          let uu____66724 =
                            let uu____66727 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____66727  in
                          FStar_Syntax_Util.arrow uu____66694 uu____66724  in
                        mk_gctx uu____66693  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____66692
                       in
                    let r =
                      let uu____66730 =
                        let uu____66731 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66731  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____66730
                       in
                    let ret1 =
                      let uu____66736 =
                        let uu____66737 =
                          let uu____66740 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66740  in
                        FStar_Syntax_Util.residual_tot uu____66737  in
                      FStar_Pervasives_Native.Some uu____66736  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____66750 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____66753 =
                          let uu____66764 =
                            let uu____66767 =
                              let uu____66768 =
                                let uu____66769 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____66769
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____66768  in
                            [uu____66767]  in
                          FStar_List.append gamma_as_args uu____66764  in
                        FStar_Syntax_Util.mk_app uu____66750 uu____66753  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____66772 =
                      let uu____66773 = mk_all_implicit binders  in
                      let uu____66780 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____66773 uu____66780  in
                    FStar_Syntax_Util.abs uu____66772 outer_body ret1  in
                  let c_app1 =
                    let uu____66832 = mk_lid "app"  in
                    register env1 uu____66832 c_app  in
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
                      let uu____66844 =
                        let uu____66853 =
                          let uu____66860 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____66860  in
                        [uu____66853]  in
                      let uu____66873 =
                        let uu____66876 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____66876  in
                      FStar_Syntax_Util.arrow uu____66844 uu____66873  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____66880 =
                        let uu____66881 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66881  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____66880
                       in
                    let ret1 =
                      let uu____66886 =
                        let uu____66887 =
                          let uu____66890 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66890  in
                        FStar_Syntax_Util.residual_tot uu____66887  in
                      FStar_Pervasives_Native.Some uu____66886  in
                    let uu____66891 =
                      let uu____66892 = mk_all_implicit binders  in
                      let uu____66899 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____66892 uu____66899  in
                    let uu____66950 =
                      let uu____66953 =
                        let uu____66964 =
                          let uu____66967 =
                            let uu____66968 =
                              let uu____66979 =
                                let uu____66982 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____66982]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____66979
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____66968  in
                          let uu____66991 =
                            let uu____66994 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____66994]  in
                          uu____66967 :: uu____66991  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____66964
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____66953  in
                    FStar_Syntax_Util.abs uu____66891 uu____66950 ret1  in
                  let c_lift11 =
                    let uu____67004 = mk_lid "lift1"  in
                    register env1 uu____67004 c_lift1  in
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
                      let uu____67018 =
                        let uu____67027 =
                          let uu____67034 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67034  in
                        let uu____67035 =
                          let uu____67044 =
                            let uu____67051 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____67051  in
                          [uu____67044]  in
                        uu____67027 :: uu____67035  in
                      let uu____67070 =
                        let uu____67073 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____67073  in
                      FStar_Syntax_Util.arrow uu____67018 uu____67070  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____67077 =
                        let uu____67078 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____67078  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____67077
                       in
                    let a2 =
                      let uu____67081 =
                        let uu____67082 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____67082  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____67081
                       in
                    let ret1 =
                      let uu____67087 =
                        let uu____67088 =
                          let uu____67091 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____67091  in
                        FStar_Syntax_Util.residual_tot uu____67088  in
                      FStar_Pervasives_Native.Some uu____67087  in
                    let uu____67092 =
                      let uu____67093 = mk_all_implicit binders  in
                      let uu____67100 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____67093 uu____67100  in
                    let uu____67165 =
                      let uu____67168 =
                        let uu____67179 =
                          let uu____67182 =
                            let uu____67183 =
                              let uu____67194 =
                                let uu____67197 =
                                  let uu____67198 =
                                    let uu____67209 =
                                      let uu____67212 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____67212]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____67209
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____67198
                                   in
                                let uu____67221 =
                                  let uu____67224 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____67224]  in
                                uu____67197 :: uu____67221  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67194
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____67183  in
                          let uu____67233 =
                            let uu____67236 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____67236]  in
                          uu____67182 :: uu____67233  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67179
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67168  in
                    FStar_Syntax_Util.abs uu____67092 uu____67165 ret1  in
                  let c_lift21 =
                    let uu____67246 = mk_lid "lift2"  in
                    register env1 uu____67246 c_lift2  in
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
                      let uu____67258 =
                        let uu____67267 =
                          let uu____67274 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67274  in
                        [uu____67267]  in
                      let uu____67287 =
                        let uu____67290 =
                          let uu____67291 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____67291  in
                        FStar_Syntax_Syntax.mk_Total uu____67290  in
                      FStar_Syntax_Util.arrow uu____67258 uu____67287  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____67297 =
                        let uu____67298 =
                          let uu____67301 =
                            let uu____67302 =
                              let uu____67311 =
                                let uu____67318 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____67318
                                 in
                              [uu____67311]  in
                            let uu____67331 =
                              let uu____67334 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____67334  in
                            FStar_Syntax_Util.arrow uu____67302 uu____67331
                             in
                          mk_ctx uu____67301  in
                        FStar_Syntax_Util.residual_tot uu____67298  in
                      FStar_Pervasives_Native.Some uu____67297  in
                    let e1 =
                      let uu____67336 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____67336
                       in
                    let body =
                      let uu____67341 =
                        let uu____67342 =
                          let uu____67351 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____67351]  in
                        FStar_List.append gamma uu____67342  in
                      let uu____67376 =
                        let uu____67379 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____67382 =
                          let uu____67393 =
                            let uu____67394 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____67394  in
                          let uu____67395 = args_of_binders1 gamma  in
                          uu____67393 :: uu____67395  in
                        FStar_Syntax_Util.mk_app uu____67379 uu____67382  in
                      FStar_Syntax_Util.abs uu____67341 uu____67376 ret1  in
                    let uu____67398 =
                      let uu____67399 = mk_all_implicit binders  in
                      let uu____67406 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____67399 uu____67406  in
                    FStar_Syntax_Util.abs uu____67398 body ret1  in
                  let c_push1 =
                    let uu____67451 = mk_lid "push"  in
                    register env1 uu____67451 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____67478 =
                        let uu____67479 =
                          let uu____67496 = args_of_binders1 binders  in
                          (c, uu____67496)  in
                        FStar_Syntax_Syntax.Tm_app uu____67479  in
                      mk1 uu____67478
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____67525 =
                        let uu____67526 =
                          let uu____67535 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____67542 =
                            let uu____67551 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____67551]  in
                          uu____67535 :: uu____67542  in
                        let uu____67576 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____67526 uu____67576  in
                      FStar_Syntax_Syntax.mk_Total uu____67525  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____67581 =
                      let uu____67582 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____67582  in
                    let uu____67597 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____67602 =
                        let uu____67605 =
                          let uu____67616 =
                            let uu____67619 =
                              let uu____67620 =
                                let uu____67631 =
                                  let uu____67640 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____67640  in
                                [uu____67631]  in
                              FStar_Syntax_Util.mk_app l_ite uu____67620  in
                            [uu____67619]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____67616
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____67605  in
                      FStar_Syntax_Util.ascribe uu____67602
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____67581 uu____67597
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____67684 = mk_lid "wp_if_then_else"  in
                    register env1 uu____67684 wp_if_then_else  in
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
                      let uu____67701 =
                        let uu____67712 =
                          let uu____67715 =
                            let uu____67716 =
                              let uu____67727 =
                                let uu____67730 =
                                  let uu____67731 =
                                    let uu____67742 =
                                      let uu____67751 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67751
                                       in
                                    [uu____67742]  in
                                  FStar_Syntax_Util.mk_app l_and uu____67731
                                   in
                                [uu____67730]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67727
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67716  in
                          let uu____67776 =
                            let uu____67779 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67779]  in
                          uu____67715 :: uu____67776  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67712
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67701  in
                    let uu____67788 =
                      let uu____67789 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67789  in
                    FStar_Syntax_Util.abs uu____67788 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____67805 = mk_lid "wp_assert"  in
                    register env1 uu____67805 wp_assert  in
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
                      let uu____67822 =
                        let uu____67833 =
                          let uu____67836 =
                            let uu____67837 =
                              let uu____67848 =
                                let uu____67851 =
                                  let uu____67852 =
                                    let uu____67863 =
                                      let uu____67872 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67872
                                       in
                                    [uu____67863]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____67852
                                   in
                                [uu____67851]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67848
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67837  in
                          let uu____67897 =
                            let uu____67900 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67900]  in
                          uu____67836 :: uu____67897  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67833
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67822  in
                    let uu____67909 =
                      let uu____67910 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67910  in
                    FStar_Syntax_Util.abs uu____67909 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____67926 = mk_lid "wp_assume"  in
                    register env1 uu____67926 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____67939 =
                        let uu____67948 =
                          let uu____67955 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____67955  in
                        [uu____67948]  in
                      let uu____67968 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____67939 uu____67968  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____67976 =
                        let uu____67987 =
                          let uu____67990 =
                            let uu____67991 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67991  in
                          let uu____68010 =
                            let uu____68013 =
                              let uu____68014 =
                                let uu____68025 =
                                  let uu____68028 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____68028]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____68025
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____68014
                               in
                            [uu____68013]  in
                          uu____67990 :: uu____68010  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67987
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67976  in
                    let uu____68045 =
                      let uu____68046 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____68046  in
                    FStar_Syntax_Util.abs uu____68045 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____68062 = mk_lid "wp_close"  in
                    register env1 uu____68062 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____68073 =
                      let uu____68074 =
                        let uu____68075 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____68075
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____68074
                       in
                    FStar_Pervasives_Native.Some uu____68073  in
                  let mk_forall1 x body =
                    let uu____68087 =
                      let uu____68094 =
                        let uu____68095 =
                          let uu____68112 =
                            let uu____68123 =
                              let uu____68132 =
                                let uu____68133 =
                                  let uu____68134 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____68134]  in
                                FStar_Syntax_Util.abs uu____68133 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____68132  in
                            [uu____68123]  in
                          (FStar_Syntax_Util.tforall, uu____68112)  in
                        FStar_Syntax_Syntax.Tm_app uu____68095  in
                      FStar_Syntax_Syntax.mk uu____68094  in
                    uu____68087 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____68195 =
                      let uu____68196 = FStar_Syntax_Subst.compress t  in
                      uu____68196.FStar_Syntax_Syntax.n  in
                    match uu____68195 with
                    | FStar_Syntax_Syntax.Tm_type uu____68200 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68233  ->
                              match uu____68233 with
                              | (b,uu____68242) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____68247 -> true  in
                  let rec is_monotonic t =
                    let uu____68260 =
                      let uu____68261 = FStar_Syntax_Subst.compress t  in
                      uu____68261.FStar_Syntax_Syntax.n  in
                    match uu____68260 with
                    | FStar_Syntax_Syntax.Tm_type uu____68265 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68298  ->
                              match uu____68298 with
                              | (b,uu____68307) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____68312 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____68386 =
                      let uu____68387 = FStar_Syntax_Subst.compress t1  in
                      uu____68387.FStar_Syntax_Syntax.n  in
                    match uu____68386 with
                    | FStar_Syntax_Syntax.Tm_type uu____68392 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____68395);
                                      FStar_Syntax_Syntax.pos = uu____68396;
                                      FStar_Syntax_Syntax.vars = uu____68397;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68441 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68441
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68451 =
                              let uu____68454 =
                                let uu____68465 =
                                  let uu____68474 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68474  in
                                [uu____68465]  in
                              FStar_Syntax_Util.mk_app x uu____68454  in
                            let uu____68491 =
                              let uu____68494 =
                                let uu____68505 =
                                  let uu____68514 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68514  in
                                [uu____68505]  in
                              FStar_Syntax_Util.mk_app y uu____68494  in
                            mk_rel1 b uu____68451 uu____68491  in
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
                             let uu____68538 =
                               let uu____68541 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68544 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68541 uu____68544  in
                             let uu____68547 =
                               let uu____68550 =
                                 let uu____68553 =
                                   let uu____68564 =
                                     let uu____68573 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68573
                                      in
                                   [uu____68564]  in
                                 FStar_Syntax_Util.mk_app x uu____68553  in
                               let uu____68590 =
                                 let uu____68593 =
                                   let uu____68604 =
                                     let uu____68613 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68613
                                      in
                                   [uu____68604]  in
                                 FStar_Syntax_Util.mk_app y uu____68593  in
                               mk_rel1 b uu____68550 uu____68590  in
                             FStar_Syntax_Util.mk_imp uu____68538 uu____68547
                              in
                           let uu____68630 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68630)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____68633);
                                      FStar_Syntax_Syntax.pos = uu____68634;
                                      FStar_Syntax_Syntax.vars = uu____68635;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68679 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68679
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68689 =
                              let uu____68692 =
                                let uu____68703 =
                                  let uu____68712 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68712  in
                                [uu____68703]  in
                              FStar_Syntax_Util.mk_app x uu____68692  in
                            let uu____68729 =
                              let uu____68732 =
                                let uu____68743 =
                                  let uu____68752 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68752  in
                                [uu____68743]  in
                              FStar_Syntax_Util.mk_app y uu____68732  in
                            mk_rel1 b uu____68689 uu____68729  in
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
                             let uu____68776 =
                               let uu____68779 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68782 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68779 uu____68782  in
                             let uu____68785 =
                               let uu____68788 =
                                 let uu____68791 =
                                   let uu____68802 =
                                     let uu____68811 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68811
                                      in
                                   [uu____68802]  in
                                 FStar_Syntax_Util.mk_app x uu____68791  in
                               let uu____68828 =
                                 let uu____68831 =
                                   let uu____68842 =
                                     let uu____68851 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68851
                                      in
                                   [uu____68842]  in
                                 FStar_Syntax_Util.mk_app y uu____68831  in
                               mk_rel1 b uu____68788 uu____68828  in
                             FStar_Syntax_Util.mk_imp uu____68776 uu____68785
                              in
                           let uu____68868 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68868)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_68907 = t1  in
                          let uu____68908 =
                            let uu____68909 =
                              let uu____68924 =
                                let uu____68927 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____68927  in
                              ([binder], uu____68924)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____68909  in
                          {
                            FStar_Syntax_Syntax.n = uu____68908;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_68907.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_68907.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____68950 ->
                        failwith "unhandled arrow"
                    | uu____68968 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____69005 =
                        let uu____69006 = FStar_Syntax_Subst.compress t1  in
                        uu____69006.FStar_Syntax_Syntax.n  in
                      match uu____69005 with
                      | FStar_Syntax_Syntax.Tm_type uu____69009 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____69036 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____69036
                          ->
                          let project i tuple =
                            let projector =
                              let uu____69057 =
                                let uu____69058 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____69058 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____69057
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____69088 =
                            let uu____69099 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____69117  ->
                                     match uu____69117 with
                                     | (t2,q) ->
                                         let uu____69137 = project i x  in
                                         let uu____69140 = project i y  in
                                         mk_stronger t2 uu____69137
                                           uu____69140) args
                               in
                            match uu____69099 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____69088 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____69194);
                                      FStar_Syntax_Syntax.pos = uu____69195;
                                      FStar_Syntax_Syntax.vars = uu____69196;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69240  ->
                                   match uu____69240 with
                                   | (bv,q) ->
                                       let uu____69254 =
                                         let uu____69256 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69256  in
                                       FStar_Syntax_Syntax.gen_bv uu____69254
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69265 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69265) bvs
                             in
                          let body =
                            let uu____69267 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69270 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69267 uu____69270  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____69279);
                                      FStar_Syntax_Syntax.pos = uu____69280;
                                      FStar_Syntax_Syntax.vars = uu____69281;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69325  ->
                                   match uu____69325 with
                                   | (bv,q) ->
                                       let uu____69339 =
                                         let uu____69341 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69341  in
                                       FStar_Syntax_Syntax.gen_bv uu____69339
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69350 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69350) bvs
                             in
                          let body =
                            let uu____69352 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69355 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69352 uu____69355  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____69362 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____69365 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____69368 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____69371 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____69365 uu____69368 uu____69371  in
                    let uu____69374 =
                      let uu____69375 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____69375  in
                    FStar_Syntax_Util.abs uu____69374 body ret_tot_type  in
                  let stronger1 =
                    let uu____69417 = mk_lid "stronger"  in
                    register env1 uu____69417 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69425 = FStar_Util.prefix gamma  in
                    match uu____69425 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____69491 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____69491
                             in
                          let uu____69496 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____69496 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____69506 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____69506  in
                              let guard_free1 =
                                let uu____69518 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____69518  in
                              let pat =
                                let uu____69522 =
                                  let uu____69533 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____69533]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____69522
                                 in
                              let pattern_guarded_body =
                                let uu____69561 =
                                  let uu____69562 =
                                    let uu____69569 =
                                      let uu____69570 =
                                        let uu____69583 =
                                          let uu____69594 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____69594]  in
                                        [uu____69583]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____69570
                                       in
                                    (body, uu____69569)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____69562  in
                                mk1 uu____69561  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____69641 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____69650 =
                            let uu____69653 =
                              let uu____69654 =
                                let uu____69657 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____69660 =
                                  let uu____69671 = args_of_binders1 wp_args
                                     in
                                  let uu____69674 =
                                    let uu____69677 =
                                      let uu____69678 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____69678
                                       in
                                    [uu____69677]  in
                                  FStar_List.append uu____69671 uu____69674
                                   in
                                FStar_Syntax_Util.mk_app uu____69657
                                  uu____69660
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____69654  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____69653
                             in
                          FStar_Syntax_Util.abs gamma uu____69650
                            ret_gtot_type
                           in
                        let uu____69679 =
                          let uu____69680 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____69680  in
                        FStar_Syntax_Util.abs uu____69679 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____69696 = mk_lid "ite_wp"  in
                    register env1 uu____69696 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69704 = FStar_Util.prefix gamma  in
                    match uu____69704 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____69762 =
                            let uu____69763 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____69770 =
                              let uu____69781 =
                                let uu____69790 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____69790  in
                              [uu____69781]  in
                            FStar_Syntax_Util.mk_app uu____69763 uu____69770
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____69762
                           in
                        let uu____69807 =
                          let uu____69808 =
                            let uu____69817 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____69817 gamma  in
                          FStar_List.append binders uu____69808  in
                        FStar_Syntax_Util.abs uu____69807 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____69839 = mk_lid "null_wp"  in
                    register env1 uu____69839 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____69852 =
                        let uu____69863 =
                          let uu____69866 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____69867 =
                            let uu____69870 =
                              let uu____69871 =
                                let uu____69882 =
                                  let uu____69891 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____69891  in
                                [uu____69882]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____69871
                               in
                            let uu____69908 =
                              let uu____69911 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____69911]  in
                            uu____69870 :: uu____69908  in
                          uu____69866 :: uu____69867  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____69863
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____69852  in
                    let uu____69920 =
                      let uu____69921 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____69921  in
                    FStar_Syntax_Util.abs uu____69920 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____69937 = mk_lid "wp_trivial"  in
                    register env1 uu____69937 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____69943 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____69943
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____69955 =
                      let uu____69956 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____69956  in
                    let uu____70004 =
                      let uu___934_70005 = ed  in
                      let uu____70006 =
                        let uu____70007 = c wp_if_then_else2  in
                        ([], uu____70007)  in
                      let uu____70014 =
                        let uu____70015 = c ite_wp2  in ([], uu____70015)  in
                      let uu____70022 =
                        let uu____70023 = c stronger2  in ([], uu____70023)
                         in
                      let uu____70030 =
                        let uu____70031 = c wp_close2  in ([], uu____70031)
                         in
                      let uu____70038 =
                        let uu____70039 = c wp_assert2  in ([], uu____70039)
                         in
                      let uu____70046 =
                        let uu____70047 = c wp_assume2  in ([], uu____70047)
                         in
                      let uu____70054 =
                        let uu____70055 = c null_wp2  in ([], uu____70055)
                         in
                      let uu____70062 =
                        let uu____70063 = c wp_trivial2  in ([], uu____70063)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_70005.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_70005.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_70005.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_70005.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_70005.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_70005.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_70005.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____70006;
                        FStar_Syntax_Syntax.ite_wp = uu____70014;
                        FStar_Syntax_Syntax.stronger = uu____70022;
                        FStar_Syntax_Syntax.close_wp = uu____70030;
                        FStar_Syntax_Syntax.assert_p = uu____70038;
                        FStar_Syntax_Syntax.assume_p = uu____70046;
                        FStar_Syntax_Syntax.null_wp = uu____70054;
                        FStar_Syntax_Syntax.trivial = uu____70062;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_70005.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_70005.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_70005.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_70005.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_70005.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____69955, uu____70004)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_70087 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_70087.subst);
        tc_const = (uu___939_70087.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____70108 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____70128 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____70149) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_70163  ->
                match uu___585_70163 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____70166 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____70168 ->
        let uu____70169 =
          let uu____70175 =
            let uu____70177 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____70177
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____70175)  in
        FStar_Errors.raise_error uu____70169 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_70187  ->
    match uu___586_70187 with
    | N t ->
        let uu____70190 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____70190
    | M t ->
        let uu____70194 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____70194
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____70203,c) -> nm_of_comp c
    | uu____70225 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____70238 = nm_of_comp c  in
    match uu____70238 with | M uu____70240 -> true | N uu____70242 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____70253 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____70269 =
        let uu____70278 =
          let uu____70285 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____70285  in
        [uu____70278]  in
      let uu____70304 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____70269 uu____70304  in
    let uu____70307 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____70307
  
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
        let uu____70349 =
          let uu____70350 =
            let uu____70365 =
              let uu____70374 =
                let uu____70381 =
                  let uu____70382 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____70382  in
                let uu____70383 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____70381, uu____70383)  in
              [uu____70374]  in
            let uu____70401 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____70365, uu____70401)  in
          FStar_Syntax_Syntax.Tm_arrow uu____70350  in
        mk1 uu____70349

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70441) ->
          let binders1 =
            FStar_List.map
              (fun uu____70487  ->
                 match uu____70487 with
                 | (bv,aqual) ->
                     let uu____70506 =
                       let uu___989_70507 = bv  in
                       let uu____70508 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_70507.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_70507.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____70508
                       }  in
                     (uu____70506, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____70513,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____70515);
                              FStar_Syntax_Syntax.pos = uu____70516;
                              FStar_Syntax_Syntax.vars = uu____70517;_})
               ->
               let uu____70546 =
                 let uu____70547 =
                   let uu____70562 =
                     let uu____70565 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____70565  in
                   (binders1, uu____70562)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____70547  in
               mk1 uu____70546
           | uu____70576 ->
               let uu____70577 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____70577 with
                | N hn ->
                    let uu____70579 =
                      let uu____70580 =
                        let uu____70595 =
                          let uu____70598 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____70598  in
                        (binders1, uu____70595)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70580  in
                    mk1 uu____70579
                | M a ->
                    let uu____70610 =
                      let uu____70611 =
                        let uu____70626 =
                          let uu____70635 =
                            let uu____70644 =
                              let uu____70651 =
                                let uu____70652 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____70652  in
                              let uu____70653 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____70651, uu____70653)  in
                            [uu____70644]  in
                          FStar_List.append binders1 uu____70635  in
                        let uu____70677 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____70626, uu____70677)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70611  in
                    mk1 uu____70610))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____70771 = f x  in
                    FStar_Util.string_builder_append strb uu____70771);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____70780 = f x1  in
                         FStar_Util.string_builder_append strb uu____70780))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____70784 =
              let uu____70790 =
                let uu____70792 = FStar_Syntax_Print.term_to_string t2  in
                let uu____70794 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____70792 uu____70794
                 in
              (FStar_Errors.Warning_DependencyFound, uu____70790)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____70784  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____70816 =
              let uu____70817 = FStar_Syntax_Subst.compress ty  in
              uu____70817.FStar_Syntax_Syntax.n  in
            match uu____70816 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____70843 =
                  let uu____70845 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____70845  in
                if uu____70843
                then false
                else
                  (try
                     (fun uu___1038_70862  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____70886 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____70886 s  in
                              let uu____70889 =
                                let uu____70891 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____70891  in
                              if uu____70889
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____70897 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____70897 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____70922  ->
                                          match uu____70922 with
                                          | (bv,uu____70934) ->
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
            | uu____70962 ->
                ((let uu____70964 =
                    let uu____70970 =
                      let uu____70972 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____70972
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____70970)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____70964);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____70988 =
              let uu____70989 = FStar_Syntax_Subst.compress head2  in
              uu____70989.FStar_Syntax_Syntax.n  in
            match uu____70988 with
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
                  (let uu____70995 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____70995)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____70998 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____70998 with
                 | ((uu____71008,ty),uu____71010) ->
                     let uu____71015 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____71015
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____71028 =
                         let uu____71029 = FStar_Syntax_Subst.compress res
                            in
                         uu____71029.FStar_Syntax_Syntax.n  in
                       (match uu____71028 with
                        | FStar_Syntax_Syntax.Tm_app uu____71033 -> true
                        | uu____71051 ->
                            ((let uu____71053 =
                                let uu____71059 =
                                  let uu____71061 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____71061
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____71059)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____71053);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____71069 -> true
            | FStar_Syntax_Syntax.Tm_name uu____71071 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71074) ->
                is_valid_application t2
            | uu____71079 -> false  in
          let uu____71081 = is_valid_application head1  in
          if uu____71081
          then
            let uu____71084 =
              let uu____71085 =
                let uu____71102 =
                  FStar_List.map
                    (fun uu____71131  ->
                       match uu____71131 with
                       | (t2,qual) ->
                           let uu____71156 = star_type' env t2  in
                           (uu____71156, qual)) args
                   in
                (head1, uu____71102)  in
              FStar_Syntax_Syntax.Tm_app uu____71085  in
            mk1 uu____71084
          else
            (let uu____71173 =
               let uu____71179 =
                 let uu____71181 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____71181
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____71179)  in
             FStar_Errors.raise_err uu____71173)
      | FStar_Syntax_Syntax.Tm_bvar uu____71185 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____71186 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____71187 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____71188 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____71216 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____71216 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_71224 = env  in
                 let uu____71225 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____71225;
                   subst = (uu___1110_71224.subst);
                   tc_const = (uu___1110_71224.tc_const)
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
               ((let uu___1125_71252 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_71252.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_71252.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____71259 =
            let uu____71260 =
              let uu____71267 = star_type' env t2  in (uu____71267, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____71260  in
          mk1 uu____71259
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____71319 =
            let uu____71320 =
              let uu____71347 = star_type' env e  in
              let uu____71350 =
                let uu____71367 =
                  let uu____71376 = star_type' env t2  in
                  FStar_Util.Inl uu____71376  in
                (uu____71367, FStar_Pervasives_Native.None)  in
              (uu____71347, uu____71350, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71320  in
          mk1 uu____71319
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____71464 =
            let uu____71465 =
              let uu____71492 = star_type' env e  in
              let uu____71495 =
                let uu____71512 =
                  let uu____71521 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____71521  in
                (uu____71512, FStar_Pervasives_Native.None)  in
              (uu____71492, uu____71495, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71465  in
          mk1 uu____71464
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____71562,(uu____71563,FStar_Pervasives_Native.Some uu____71564),uu____71565)
          ->
          let uu____71614 =
            let uu____71620 =
              let uu____71622 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____71622
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71620)  in
          FStar_Errors.raise_err uu____71614
      | FStar_Syntax_Syntax.Tm_refine uu____71626 ->
          let uu____71633 =
            let uu____71639 =
              let uu____71641 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____71641
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71639)  in
          FStar_Errors.raise_err uu____71633
      | FStar_Syntax_Syntax.Tm_uinst uu____71645 ->
          let uu____71652 =
            let uu____71658 =
              let uu____71660 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____71660
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71658)  in
          FStar_Errors.raise_err uu____71652
      | FStar_Syntax_Syntax.Tm_quoted uu____71664 ->
          let uu____71671 =
            let uu____71677 =
              let uu____71679 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____71679
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71677)  in
          FStar_Errors.raise_err uu____71671
      | FStar_Syntax_Syntax.Tm_constant uu____71683 ->
          let uu____71684 =
            let uu____71690 =
              let uu____71692 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____71692
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71690)  in
          FStar_Errors.raise_err uu____71684
      | FStar_Syntax_Syntax.Tm_match uu____71696 ->
          let uu____71719 =
            let uu____71725 =
              let uu____71727 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____71727
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71725)  in
          FStar_Errors.raise_err uu____71719
      | FStar_Syntax_Syntax.Tm_let uu____71731 ->
          let uu____71745 =
            let uu____71751 =
              let uu____71753 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____71753
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71751)  in
          FStar_Errors.raise_err uu____71745
      | FStar_Syntax_Syntax.Tm_uvar uu____71757 ->
          let uu____71770 =
            let uu____71776 =
              let uu____71778 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____71778
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71776)  in
          FStar_Errors.raise_err uu____71770
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71782 =
            let uu____71788 =
              let uu____71790 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____71790
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71788)  in
          FStar_Errors.raise_err uu____71782
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71795 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____71795
      | FStar_Syntax_Syntax.Tm_delayed uu____71798 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_71830  ->
    match uu___588_71830 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_71841  ->
                match uu___587_71841 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____71844 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____71854 =
      let uu____71855 = FStar_Syntax_Subst.compress t  in
      uu____71855.FStar_Syntax_Syntax.n  in
    match uu____71854 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____71887 =
            let uu____71888 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____71888  in
          is_C uu____71887  in
        if r
        then
          ((let uu____71912 =
              let uu____71914 =
                FStar_List.for_all
                  (fun uu____71925  ->
                     match uu____71925 with | (h,uu____71934) -> is_C h) args
                 in
              Prims.op_Negation uu____71914  in
            if uu____71912 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____71947 =
              let uu____71949 =
                FStar_List.for_all
                  (fun uu____71961  ->
                     match uu____71961 with
                     | (h,uu____71970) ->
                         let uu____71975 = is_C h  in
                         Prims.op_Negation uu____71975) args
                 in
              Prims.op_Negation uu____71949  in
            if uu____71947 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____72004 = nm_of_comp comp  in
        (match uu____72004 with
         | M t1 ->
             ((let uu____72008 = is_C t1  in
               if uu____72008 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____72017) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____72023) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____72029,uu____72030) -> is_C t1
    | uu____72071 -> false
  
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
          let uu____72107 =
            let uu____72108 =
              let uu____72125 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____72128 =
                let uu____72139 =
                  let uu____72148 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____72148)  in
                [uu____72139]  in
              (uu____72125, uu____72128)  in
            FStar_Syntax_Syntax.Tm_app uu____72108  in
          mk1 uu____72107  in
        let uu____72184 =
          let uu____72185 = FStar_Syntax_Syntax.mk_binder p  in [uu____72185]
           in
        FStar_Syntax_Util.abs uu____72184 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_72210  ->
    match uu___589_72210 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____72213 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____72451 =
          match uu____72451 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____72488 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____72491 =
                       let uu____72493 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____72493  in
                     Prims.op_Negation uu____72491)
                   in
                if uu____72488
                then
                  let uu____72495 =
                    let uu____72501 =
                      let uu____72503 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____72505 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____72507 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____72503 uu____72505 uu____72507
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____72501)  in
                  FStar_Errors.raise_err uu____72495
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____72532 = mk_return env t1 s_e  in
                     ((M t1), uu____72532, u_e)))
               | (M t1,N t2) ->
                   let uu____72539 =
                     let uu____72545 =
                       let uu____72547 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____72549 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____72551 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____72547 uu____72549 uu____72551
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____72545)
                      in
                   FStar_Errors.raise_err uu____72539)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_72603 =
            match uu___590_72603 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____72619 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____72640 =
                let uu____72646 =
                  let uu____72648 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____72648
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____72646)  in
              FStar_Errors.raise_error uu____72640 e2.FStar_Syntax_Syntax.pos
          | M uu____72658 ->
              let uu____72659 = check env1 e2 context_nm  in
              strip_m uu____72659
           in
        let uu____72666 =
          let uu____72667 = FStar_Syntax_Subst.compress e  in
          uu____72667.FStar_Syntax_Syntax.n  in
        match uu____72666 with
        | FStar_Syntax_Syntax.Tm_bvar uu____72676 ->
            let uu____72677 = infer env e  in return_if uu____72677
        | FStar_Syntax_Syntax.Tm_name uu____72684 ->
            let uu____72685 = infer env e  in return_if uu____72685
        | FStar_Syntax_Syntax.Tm_fvar uu____72692 ->
            let uu____72693 = infer env e  in return_if uu____72693
        | FStar_Syntax_Syntax.Tm_abs uu____72700 ->
            let uu____72719 = infer env e  in return_if uu____72719
        | FStar_Syntax_Syntax.Tm_constant uu____72726 ->
            let uu____72727 = infer env e  in return_if uu____72727
        | FStar_Syntax_Syntax.Tm_quoted uu____72734 ->
            let uu____72741 = infer env e  in return_if uu____72741
        | FStar_Syntax_Syntax.Tm_app uu____72748 ->
            let uu____72765 = infer env e  in return_if uu____72765
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____72773 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____72773 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____72838) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____72844) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____72850,uu____72851) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____72892 ->
            let uu____72906 =
              let uu____72908 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____72908  in
            failwith uu____72906
        | FStar_Syntax_Syntax.Tm_type uu____72917 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____72925 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____72947 ->
            let uu____72954 =
              let uu____72956 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____72956  in
            failwith uu____72954
        | FStar_Syntax_Syntax.Tm_uvar uu____72965 ->
            let uu____72978 =
              let uu____72980 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____72980  in
            failwith uu____72978
        | FStar_Syntax_Syntax.Tm_delayed uu____72989 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____73019 =
              let uu____73021 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____73021  in
            failwith uu____73019

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
      let uu____73051 =
        let uu____73052 = FStar_Syntax_Subst.compress e  in
        uu____73052.FStar_Syntax_Syntax.n  in
      match uu____73051 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____73071 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____73071
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____73122;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____73123;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____73129 =
                  let uu___1360_73130 = rc  in
                  let uu____73131 =
                    let uu____73136 =
                      let uu____73139 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____73139  in
                    FStar_Pervasives_Native.Some uu____73136  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_73130.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____73131;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_73130.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____73129
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_73151 = env  in
            let uu____73152 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____73152;
              subst = (uu___1366_73151.subst);
              tc_const = (uu___1366_73151.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____73178  ->
                 match uu____73178 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_73201 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_73201.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_73201.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____73202 =
            FStar_List.fold_left
              (fun uu____73233  ->
                 fun uu____73234  ->
                   match (uu____73233, uu____73234) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____73292 = is_C c  in
                       if uu____73292
                       then
                         let xw =
                           let uu____73302 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____73302
                            in
                         let x =
                           let uu___1385_73305 = bv  in
                           let uu____73306 =
                             let uu____73309 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____73309  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_73305.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_73305.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____73306
                           }  in
                         let env3 =
                           let uu___1388_73311 = env2  in
                           let uu____73312 =
                             let uu____73315 =
                               let uu____73316 =
                                 let uu____73323 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____73323)  in
                               FStar_Syntax_Syntax.NT uu____73316  in
                             uu____73315 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_73311.tcenv);
                             subst = uu____73312;
                             tc_const = (uu___1388_73311.tc_const)
                           }  in
                         let uu____73328 =
                           let uu____73331 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____73332 =
                             let uu____73335 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____73335 :: acc  in
                           uu____73331 :: uu____73332  in
                         (env3, uu____73328)
                       else
                         (let x =
                            let uu___1391_73341 = bv  in
                            let uu____73342 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_73341.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_73341.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____73342
                            }  in
                          let uu____73345 =
                            let uu____73348 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____73348 :: acc  in
                          (env2, uu____73345))) (env1, []) binders1
             in
          (match uu____73202 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____73368 =
                 let check_what =
                   let uu____73394 = is_monadic rc_opt1  in
                   if uu____73394 then check_m else check_n  in
                 let uu____73411 = check_what env2 body1  in
                 match uu____73411 with
                 | (t,s_body,u_body) ->
                     let uu____73431 =
                       let uu____73434 =
                         let uu____73435 = is_monadic rc_opt1  in
                         if uu____73435 then M t else N t  in
                       comp_of_nm uu____73434  in
                     (uu____73431, s_body, u_body)
                  in
               (match uu____73368 with
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
                                 let uu____73475 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_73481  ->
                                           match uu___591_73481 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____73484 -> false))
                                    in
                                 if uu____73475
                                 then
                                   let uu____73487 =
                                     FStar_List.filter
                                       (fun uu___592_73491  ->
                                          match uu___592_73491 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____73494 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____73487
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____73505 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_73511  ->
                                         match uu___593_73511 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____73514 -> false))
                                  in
                               if uu____73505
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_73523  ->
                                        match uu___594_73523 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____73526 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____73528 =
                                   let uu____73529 =
                                     let uu____73534 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____73534
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____73529 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____73528
                               else
                                 (let uu____73541 =
                                    let uu___1432_73542 = rc  in
                                    let uu____73543 =
                                      let uu____73548 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____73548
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_73542.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____73543;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_73542.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____73541))
                       in
                    let uu____73553 =
                      let comp1 =
                        let uu____73561 = is_monadic rc_opt1  in
                        let uu____73563 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____73561 uu____73563
                         in
                      let uu____73564 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____73564,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____73553 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____73602 =
                             let uu____73603 =
                               let uu____73622 =
                                 let uu____73625 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____73625 s_rc_opt  in
                               (s_binders1, s_body1, uu____73622)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73603  in
                           mk1 uu____73602  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____73645 =
                             let uu____73646 =
                               let uu____73665 =
                                 let uu____73668 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____73668 u_rc_opt  in
                               (u_binders2, u_body2, uu____73665)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73646  in
                           mk1 uu____73645  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____73684;_};
            FStar_Syntax_Syntax.fv_delta = uu____73685;
            FStar_Syntax_Syntax.fv_qual = uu____73686;_}
          ->
          let uu____73689 =
            let uu____73694 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____73694  in
          (match uu____73689 with
           | (uu____73725,t) ->
               let uu____73727 =
                 let uu____73728 = normalize1 t  in N uu____73728  in
               (uu____73727, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____73729;
             FStar_Syntax_Syntax.vars = uu____73730;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73809 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73809 with
           | (unary_op1,uu____73833) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____73904;
             FStar_Syntax_Syntax.vars = uu____73905;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____74001 = FStar_Syntax_Util.head_and_args e  in
          (match uu____74001 with
           | (unary_op1,uu____74025) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74104;
             FStar_Syntax_Syntax.vars = uu____74105;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____74143 = infer env a  in
          (match uu____74143 with
           | (t,s,u) ->
               let uu____74159 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74159 with
                | (head1,uu____74183) ->
                    let uu____74208 =
                      let uu____74209 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____74209  in
                    let uu____74210 =
                      let uu____74211 =
                        let uu____74212 =
                          let uu____74229 =
                            let uu____74240 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74240]  in
                          (head1, uu____74229)  in
                        FStar_Syntax_Syntax.Tm_app uu____74212  in
                      mk1 uu____74211  in
                    let uu____74277 =
                      let uu____74278 =
                        let uu____74279 =
                          let uu____74296 =
                            let uu____74307 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74307]  in
                          (head1, uu____74296)  in
                        FStar_Syntax_Syntax.Tm_app uu____74279  in
                      mk1 uu____74278  in
                    (uu____74208, uu____74210, uu____74277)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74344;
             FStar_Syntax_Syntax.vars = uu____74345;_},(a1,uu____74347)::a2::[])
          ->
          let uu____74403 = infer env a1  in
          (match uu____74403 with
           | (t,s,u) ->
               let uu____74419 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74419 with
                | (head1,uu____74443) ->
                    let uu____74468 =
                      let uu____74469 =
                        let uu____74470 =
                          let uu____74487 =
                            let uu____74498 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74498; a2]  in
                          (head1, uu____74487)  in
                        FStar_Syntax_Syntax.Tm_app uu____74470  in
                      mk1 uu____74469  in
                    let uu____74543 =
                      let uu____74544 =
                        let uu____74545 =
                          let uu____74562 =
                            let uu____74573 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74573; a2]  in
                          (head1, uu____74562)  in
                        FStar_Syntax_Syntax.Tm_app uu____74545  in
                      mk1 uu____74544  in
                    (t, uu____74468, uu____74543)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74618;
             FStar_Syntax_Syntax.vars = uu____74619;_},uu____74620)
          ->
          let uu____74645 =
            let uu____74651 =
              let uu____74653 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74653
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74651)  in
          FStar_Errors.raise_error uu____74645 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74663;
             FStar_Syntax_Syntax.vars = uu____74664;_},uu____74665)
          ->
          let uu____74690 =
            let uu____74696 =
              let uu____74698 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74698
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74696)  in
          FStar_Errors.raise_error uu____74690 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____74734 = check_n env head1  in
          (match uu____74734 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____74757 =
                   let uu____74758 = FStar_Syntax_Subst.compress t  in
                   uu____74758.FStar_Syntax_Syntax.n  in
                 match uu____74757 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____74762 -> true
                 | uu____74778 -> false  in
               let rec flatten1 t =
                 let uu____74800 =
                   let uu____74801 = FStar_Syntax_Subst.compress t  in
                   uu____74801.FStar_Syntax_Syntax.n  in
                 match uu____74800 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____74820);
                                FStar_Syntax_Syntax.pos = uu____74821;
                                FStar_Syntax_Syntax.vars = uu____74822;_})
                     when is_arrow t1 ->
                     let uu____74851 = flatten1 t1  in
                     (match uu____74851 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____74951,uu____74952) -> flatten1 e1
                 | uu____74993 ->
                     let uu____74994 =
                       let uu____75000 =
                         let uu____75002 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____75002
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____75000)  in
                     FStar_Errors.raise_err uu____74994
                  in
               let uu____75020 = flatten1 t_head  in
               (match uu____75020 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____75095 =
                          let uu____75101 =
                            let uu____75103 = FStar_Util.string_of_int n1  in
                            let uu____75111 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____75123 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____75103 uu____75111 uu____75123
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____75101)
                           in
                        FStar_Errors.raise_err uu____75095)
                     else ();
                     (let uu____75135 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____75135 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____75188 args1 =
                            match uu____75188 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____75288 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____75288
                                 | (binders3,[]) ->
                                     let uu____75326 =
                                       let uu____75327 =
                                         let uu____75330 =
                                           let uu____75331 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____75331
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____75330
                                          in
                                       uu____75327.FStar_Syntax_Syntax.n  in
                                     (match uu____75326 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____75364 =
                                            let uu____75365 =
                                              let uu____75366 =
                                                let uu____75381 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____75381)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____75366
                                               in
                                            mk1 uu____75365  in
                                          N uu____75364
                                      | uu____75394 -> failwith "wat?")
                                 | ([],uu____75396::uu____75397) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____75450)::binders3,(arg,uu____75453)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____75540 = FStar_List.splitAt n' binders1
                             in
                          (match uu____75540 with
                           | (binders2,uu____75578) ->
                               let uu____75611 =
                                 let uu____75634 =
                                   FStar_List.map2
                                     (fun uu____75696  ->
                                        fun uu____75697  ->
                                          match (uu____75696, uu____75697)
                                          with
                                          | ((bv,uu____75745),(arg,q)) ->
                                              let uu____75774 =
                                                let uu____75775 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____75775.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____75774 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____75796 ->
                                                   let uu____75797 =
                                                     let uu____75804 =
                                                       star_type' env arg  in
                                                     (uu____75804, q)  in
                                                   (uu____75797, [(arg, q)])
                                               | uu____75841 ->
                                                   let uu____75842 =
                                                     check_n env arg  in
                                                   (match uu____75842 with
                                                    | (uu____75867,s_arg,u_arg)
                                                        ->
                                                        let uu____75870 =
                                                          let uu____75879 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____75879
                                                          then
                                                            let uu____75890 =
                                                              let uu____75897
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____75897,
                                                                q)
                                                               in
                                                            [uu____75890;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____75870))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____75634  in
                               (match uu____75611 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____76025 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____76038 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____76025, uu____76038)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____76107) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____76113) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____76119,uu____76120) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____76162 =
            let uu____76163 = env.tc_const c  in N uu____76163  in
          (uu____76162, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____76170 ->
          let uu____76184 =
            let uu____76186 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____76186  in
          failwith uu____76184
      | FStar_Syntax_Syntax.Tm_type uu____76195 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____76203 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____76225 ->
          let uu____76232 =
            let uu____76234 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____76234  in
          failwith uu____76232
      | FStar_Syntax_Syntax.Tm_uvar uu____76243 ->
          let uu____76256 =
            let uu____76258 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____76258  in
          failwith uu____76256
      | FStar_Syntax_Syntax.Tm_delayed uu____76267 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____76297 =
            let uu____76299 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____76299  in
          failwith uu____76297

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
          let uu____76348 = check_n env e0  in
          match uu____76348 with
          | (uu____76361,s_e0,u_e0) ->
              let uu____76364 =
                let uu____76393 =
                  FStar_List.map
                    (fun b  ->
                       let uu____76454 = FStar_Syntax_Subst.open_branch b  in
                       match uu____76454 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_76496 = env  in
                             let uu____76497 =
                               let uu____76498 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____76498
                                in
                             {
                               tcenv = uu____76497;
                               subst = (uu___1707_76496.subst);
                               tc_const = (uu___1707_76496.tc_const)
                             }  in
                           let uu____76501 = f env1 body  in
                           (match uu____76501 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____76573 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____76393  in
              (match uu____76364 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____76679 = FStar_List.hd nms  in
                     match uu____76679 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_76688  ->
                          match uu___595_76688 with
                          | M uu____76690 -> true
                          | uu____76692 -> false) nms
                      in
                   let uu____76694 =
                     let uu____76731 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____76821  ->
                              match uu____76821 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____77005 =
                                         check env original_body (M t2)  in
                                       (match uu____77005 with
                                        | (uu____77042,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____77081,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____76731  in
                   (match uu____76694 with
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
                              (fun uu____77270  ->
                                 match uu____77270 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____77321 =
                                         let uu____77322 =
                                           let uu____77339 =
                                             let uu____77350 =
                                               let uu____77359 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____77362 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____77359, uu____77362)  in
                                             [uu____77350]  in
                                           (s_body, uu____77339)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____77322
                                          in
                                       mk1 uu____77321  in
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
                            let uu____77497 =
                              let uu____77498 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____77498]  in
                            let uu____77517 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____77497 uu____77517
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____77541 =
                              let uu____77550 =
                                let uu____77557 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____77557
                                 in
                              [uu____77550]  in
                            let uu____77576 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____77541 uu____77576
                             in
                          let uu____77579 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____77618 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____77579, uu____77618)
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
                           let uu____77728 =
                             let uu____77729 =
                               let uu____77730 =
                                 let uu____77757 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____77757,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____77730
                                in
                             mk1 uu____77729  in
                           let uu____77816 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____77728, uu____77816))))

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
              let uu____77881 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____77881]  in
            let uu____77900 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____77900 with
            | (x_binders1,e21) ->
                let uu____77913 = infer env e1  in
                (match uu____77913 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____77930 = is_C t1  in
                       if uu____77930
                       then
                         let uu___1793_77933 = binding  in
                         let uu____77934 =
                           let uu____77937 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____77937  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_77933.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_77933.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____77934;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_77933.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_77933.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_77933.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_77933.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_77941 = env  in
                       let uu____77942 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_77944 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_77944.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_77944.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____77942;
                         subst = (uu___1796_77941.subst);
                         tc_const = (uu___1796_77941.tc_const)
                       }  in
                     let uu____77945 = proceed env1 e21  in
                     (match uu____77945 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_77962 = binding  in
                            let uu____77963 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_77962.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_77962.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____77963;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_77962.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_77962.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_77962.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_77962.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____77966 =
                            let uu____77967 =
                              let uu____77968 =
                                let uu____77982 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_77999 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_77999.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_77999.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_77999.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_77999.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_77999.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_77999.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____77982)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77968  in
                            mk1 uu____77967  in
                          let uu____78000 =
                            let uu____78001 =
                              let uu____78002 =
                                let uu____78016 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_78033 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_78033.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_78033.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_78033.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_78033.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_78033.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_78033.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78016)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78002  in
                            mk1 uu____78001  in
                          (nm_rec, uu____77966, uu____78000))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_78038 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_78038.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_78038.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_78038.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_78038.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_78038.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_78040 = env  in
                       let uu____78041 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_78043 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_78043.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_78043.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____78041;
                         subst = (uu___1820_78040.subst);
                         tc_const = (uu___1820_78040.tc_const)
                       }  in
                     let uu____78044 = ensure_m env1 e21  in
                     (match uu____78044 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____78068 =
                              let uu____78069 =
                                let uu____78086 =
                                  let uu____78097 =
                                    let uu____78106 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____78109 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78106, uu____78109)  in
                                  [uu____78097]  in
                                (s_e2, uu____78086)  in
                              FStar_Syntax_Syntax.Tm_app uu____78069  in
                            mk1 uu____78068  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____78151 =
                              let uu____78152 =
                                let uu____78169 =
                                  let uu____78180 =
                                    let uu____78189 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____78189)  in
                                  [uu____78180]  in
                                (s_e1, uu____78169)  in
                              FStar_Syntax_Syntax.Tm_app uu____78152  in
                            mk1 uu____78151  in
                          let uu____78225 =
                            let uu____78226 =
                              let uu____78227 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____78227]  in
                            FStar_Syntax_Util.abs uu____78226 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____78246 =
                            let uu____78247 =
                              let uu____78248 =
                                let uu____78262 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_78279 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_78279.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_78279.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_78279.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_78279.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_78279.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_78279.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78262)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78248  in
                            mk1 uu____78247  in
                          ((M t2), uu____78225, uu____78246)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78289 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____78289  in
      let uu____78290 = check env e mn  in
      match uu____78290 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78306 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78329 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____78329  in
      let uu____78330 = check env e mn  in
      match uu____78330 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78346 -> failwith "[check_m]: impossible"

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
        (let uu____78379 =
           let uu____78381 = is_C c  in Prims.op_Negation uu____78381  in
         if uu____78379 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____78395 =
           let uu____78396 = FStar_Syntax_Subst.compress c  in
           uu____78396.FStar_Syntax_Syntax.n  in
         match uu____78395 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____78425 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____78425 with
              | (wp_head,wp_args) ->
                  ((let uu____78469 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____78488 =
                           let uu____78490 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____78490
                            in
                         Prims.op_Negation uu____78488)
                       in
                    if uu____78469 then failwith "mismatch" else ());
                   (let uu____78503 =
                      let uu____78504 =
                        let uu____78521 =
                          FStar_List.map2
                            (fun uu____78559  ->
                               fun uu____78560  ->
                                 match (uu____78559, uu____78560) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____78622 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____78622
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____78631 =
                                         let uu____78633 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____78633 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____78631
                                       then
                                         let uu____78635 =
                                           let uu____78641 =
                                             let uu____78643 =
                                               print_implicit q  in
                                             let uu____78645 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____78643 uu____78645
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____78641)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____78635
                                       else ());
                                      (let uu____78651 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____78651, q)))) args wp_args
                           in
                        (head1, uu____78521)  in
                      FStar_Syntax_Syntax.Tm_app uu____78504  in
                    mk1 uu____78503)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____78697 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____78697 with
              | (binders_orig,comp1) ->
                  let uu____78704 =
                    let uu____78721 =
                      FStar_List.map
                        (fun uu____78761  ->
                           match uu____78761 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____78789 = is_C h  in
                               if uu____78789
                               then
                                 let w' =
                                   let uu____78805 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____78805
                                    in
                                 let uu____78807 =
                                   let uu____78816 =
                                     let uu____78825 =
                                       let uu____78832 =
                                         let uu____78833 =
                                           let uu____78834 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____78834  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____78833
                                          in
                                       (uu____78832, q)  in
                                     [uu____78825]  in
                                   (w', q) :: uu____78816  in
                                 (w', uu____78807)
                               else
                                 (let x =
                                    let uu____78868 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____78868
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____78721  in
                  (match uu____78704 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____78942 =
                           let uu____78945 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____78945
                            in
                         FStar_Syntax_Subst.subst_comp uu____78942 comp1  in
                       let app =
                         let uu____78949 =
                           let uu____78950 =
                             let uu____78967 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____78986 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____78987 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78986, uu____78987)) bvs
                                in
                             (wp, uu____78967)  in
                           FStar_Syntax_Syntax.Tm_app uu____78950  in
                         mk1 uu____78949  in
                       let comp3 =
                         let uu____79002 = type_of_comp comp2  in
                         let uu____79003 = is_monadic_comp comp2  in
                         trans_G env uu____79002 uu____79003 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____79006,uu____79007) ->
             trans_F_ env e wp
         | uu____79048 -> failwith "impossible trans_F_")

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
            let uu____79056 =
              let uu____79057 = star_type' env h  in
              let uu____79060 =
                let uu____79071 =
                  let uu____79080 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____79080)  in
                [uu____79071]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____79057;
                FStar_Syntax_Syntax.effect_args = uu____79060;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____79056
          else
            (let uu____79106 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____79106)

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
    fun t  -> let uu____79127 = n env.tcenv t  in star_type' env uu____79127
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____79147 = n env.tcenv t  in check_n env uu____79147
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____79164 = n env.tcenv c  in
        let uu____79165 = n env.tcenv wp  in
        trans_F_ env uu____79164 uu____79165
  