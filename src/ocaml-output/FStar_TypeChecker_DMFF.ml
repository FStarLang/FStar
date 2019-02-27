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
              let uu___613_65865 = a  in
              let uu____65866 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_65865.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_65865.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____65866
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____65879 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____65879
             then
               (d "Elaborating extra WP combinators";
                (let uu____65885 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____65885))
             else ());
            (let rec collect_binders t =
               let uu____65904 =
                 let uu____65905 =
                   let uu____65908 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____65908
                    in
                 uu____65905.FStar_Syntax_Syntax.n  in
               match uu____65904 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____65943) -> t1
                     | uu____65952 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____65954 = collect_binders rest  in
                   FStar_List.append bs uu____65954
               | FStar_Syntax_Syntax.Tm_type uu____65969 -> []
               | uu____65976 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____66003 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____66003
                 FStar_Syntax_Util.name_binders
                in
             (let uu____66029 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____66029
              then
                let uu____66033 =
                  let uu____66035 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____66035  in
                d uu____66033
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____66073 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____66073 with
                | (sigelt,fv) ->
                    ((let uu____66081 =
                        let uu____66084 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____66084
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____66081);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____66208  ->
                     match uu____66208 with
                     | (t,b) ->
                         let uu____66222 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____66222))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____66261 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____66261))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____66295 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____66295)
                 in
              let uu____66298 =
                let uu____66315 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____66340 =
                        let uu____66343 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____66343  in
                      FStar_Syntax_Util.arrow gamma uu____66340  in
                    let uu____66344 =
                      let uu____66345 =
                        let uu____66354 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____66361 =
                          let uu____66370 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____66370]  in
                        uu____66354 :: uu____66361  in
                      FStar_List.append binders uu____66345  in
                    FStar_Syntax_Util.abs uu____66344 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____66401 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____66402 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____66401, uu____66402)  in
                match uu____66315 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____66444 =
                        let uu____66445 =
                          let uu____66462 =
                            let uu____66473 =
                              FStar_List.map
                                (fun uu____66495  ->
                                   match uu____66495 with
                                   | (bv,uu____66507) ->
                                       let uu____66512 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____66513 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____66512, uu____66513)) binders
                               in
                            let uu____66515 =
                              let uu____66522 =
                                let uu____66527 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____66528 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____66527, uu____66528)  in
                              let uu____66530 =
                                let uu____66537 =
                                  let uu____66542 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____66542)  in
                                [uu____66537]  in
                              uu____66522 :: uu____66530  in
                            FStar_List.append uu____66473 uu____66515  in
                          (fv, uu____66462)  in
                        FStar_Syntax_Syntax.Tm_app uu____66445  in
                      mk1 uu____66444  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____66298 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____66615 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____66615
                       in
                    let ret1 =
                      let uu____66620 =
                        let uu____66621 =
                          let uu____66624 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____66624  in
                        FStar_Syntax_Util.residual_tot uu____66621  in
                      FStar_Pervasives_Native.Some uu____66620  in
                    let body =
                      let uu____66628 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____66628 ret1  in
                    let uu____66631 =
                      let uu____66632 = mk_all_implicit binders  in
                      let uu____66639 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____66632 uu____66639  in
                    FStar_Syntax_Util.abs uu____66631 body ret1  in
                  let c_pure1 =
                    let uu____66677 = mk_lid "pure"  in
                    register env1 uu____66677 c_pure  in
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
                      let uu____66687 =
                        let uu____66688 =
                          let uu____66689 =
                            let uu____66698 =
                              let uu____66705 =
                                let uu____66706 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____66706
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____66705  in
                            [uu____66698]  in
                          let uu____66719 =
                            let uu____66722 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____66722  in
                          FStar_Syntax_Util.arrow uu____66689 uu____66719  in
                        mk_gctx uu____66688  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____66687
                       in
                    let r =
                      let uu____66725 =
                        let uu____66726 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66726  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____66725
                       in
                    let ret1 =
                      let uu____66731 =
                        let uu____66732 =
                          let uu____66735 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66735  in
                        FStar_Syntax_Util.residual_tot uu____66732  in
                      FStar_Pervasives_Native.Some uu____66731  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____66745 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____66748 =
                          let uu____66759 =
                            let uu____66762 =
                              let uu____66763 =
                                let uu____66764 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____66764
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____66763  in
                            [uu____66762]  in
                          FStar_List.append gamma_as_args uu____66759  in
                        FStar_Syntax_Util.mk_app uu____66745 uu____66748  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____66767 =
                      let uu____66768 = mk_all_implicit binders  in
                      let uu____66775 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____66768 uu____66775  in
                    FStar_Syntax_Util.abs uu____66767 outer_body ret1  in
                  let c_app1 =
                    let uu____66827 = mk_lid "app"  in
                    register env1 uu____66827 c_app  in
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
                      let uu____66839 =
                        let uu____66848 =
                          let uu____66855 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____66855  in
                        [uu____66848]  in
                      let uu____66868 =
                        let uu____66871 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____66871  in
                      FStar_Syntax_Util.arrow uu____66839 uu____66868  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____66875 =
                        let uu____66876 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66876  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____66875
                       in
                    let ret1 =
                      let uu____66881 =
                        let uu____66882 =
                          let uu____66885 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66885  in
                        FStar_Syntax_Util.residual_tot uu____66882  in
                      FStar_Pervasives_Native.Some uu____66881  in
                    let uu____66886 =
                      let uu____66887 = mk_all_implicit binders  in
                      let uu____66894 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____66887 uu____66894  in
                    let uu____66945 =
                      let uu____66948 =
                        let uu____66959 =
                          let uu____66962 =
                            let uu____66963 =
                              let uu____66974 =
                                let uu____66977 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____66977]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____66974
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____66963  in
                          let uu____66986 =
                            let uu____66989 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____66989]  in
                          uu____66962 :: uu____66986  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____66959
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____66948  in
                    FStar_Syntax_Util.abs uu____66886 uu____66945 ret1  in
                  let c_lift11 =
                    let uu____66999 = mk_lid "lift1"  in
                    register env1 uu____66999 c_lift1  in
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
                      let uu____67013 =
                        let uu____67022 =
                          let uu____67029 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67029  in
                        let uu____67030 =
                          let uu____67039 =
                            let uu____67046 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____67046  in
                          [uu____67039]  in
                        uu____67022 :: uu____67030  in
                      let uu____67065 =
                        let uu____67068 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____67068  in
                      FStar_Syntax_Util.arrow uu____67013 uu____67065  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____67072 =
                        let uu____67073 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____67073  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____67072
                       in
                    let a2 =
                      let uu____67076 =
                        let uu____67077 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____67077  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____67076
                       in
                    let ret1 =
                      let uu____67082 =
                        let uu____67083 =
                          let uu____67086 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____67086  in
                        FStar_Syntax_Util.residual_tot uu____67083  in
                      FStar_Pervasives_Native.Some uu____67082  in
                    let uu____67087 =
                      let uu____67088 = mk_all_implicit binders  in
                      let uu____67095 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____67088 uu____67095  in
                    let uu____67160 =
                      let uu____67163 =
                        let uu____67174 =
                          let uu____67177 =
                            let uu____67178 =
                              let uu____67189 =
                                let uu____67192 =
                                  let uu____67193 =
                                    let uu____67204 =
                                      let uu____67207 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____67207]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____67204
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____67193
                                   in
                                let uu____67216 =
                                  let uu____67219 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____67219]  in
                                uu____67192 :: uu____67216  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67189
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____67178  in
                          let uu____67228 =
                            let uu____67231 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____67231]  in
                          uu____67177 :: uu____67228  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67174
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67163  in
                    FStar_Syntax_Util.abs uu____67087 uu____67160 ret1  in
                  let c_lift21 =
                    let uu____67241 = mk_lid "lift2"  in
                    register env1 uu____67241 c_lift2  in
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
                      let uu____67253 =
                        let uu____67262 =
                          let uu____67269 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67269  in
                        [uu____67262]  in
                      let uu____67282 =
                        let uu____67285 =
                          let uu____67286 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____67286  in
                        FStar_Syntax_Syntax.mk_Total uu____67285  in
                      FStar_Syntax_Util.arrow uu____67253 uu____67282  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____67292 =
                        let uu____67293 =
                          let uu____67296 =
                            let uu____67297 =
                              let uu____67306 =
                                let uu____67313 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____67313
                                 in
                              [uu____67306]  in
                            let uu____67326 =
                              let uu____67329 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____67329  in
                            FStar_Syntax_Util.arrow uu____67297 uu____67326
                             in
                          mk_ctx uu____67296  in
                        FStar_Syntax_Util.residual_tot uu____67293  in
                      FStar_Pervasives_Native.Some uu____67292  in
                    let e1 =
                      let uu____67331 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____67331
                       in
                    let body =
                      let uu____67336 =
                        let uu____67337 =
                          let uu____67346 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____67346]  in
                        FStar_List.append gamma uu____67337  in
                      let uu____67371 =
                        let uu____67374 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____67377 =
                          let uu____67388 =
                            let uu____67389 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____67389  in
                          let uu____67390 = args_of_binders1 gamma  in
                          uu____67388 :: uu____67390  in
                        FStar_Syntax_Util.mk_app uu____67374 uu____67377  in
                      FStar_Syntax_Util.abs uu____67336 uu____67371 ret1  in
                    let uu____67393 =
                      let uu____67394 = mk_all_implicit binders  in
                      let uu____67401 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____67394 uu____67401  in
                    FStar_Syntax_Util.abs uu____67393 body ret1  in
                  let c_push1 =
                    let uu____67446 = mk_lid "push"  in
                    register env1 uu____67446 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____67473 =
                        let uu____67474 =
                          let uu____67491 = args_of_binders1 binders  in
                          (c, uu____67491)  in
                        FStar_Syntax_Syntax.Tm_app uu____67474  in
                      mk1 uu____67473
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____67520 =
                        let uu____67521 =
                          let uu____67530 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____67537 =
                            let uu____67546 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____67546]  in
                          uu____67530 :: uu____67537  in
                        let uu____67571 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____67521 uu____67571  in
                      FStar_Syntax_Syntax.mk_Total uu____67520  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____67576 =
                      let uu____67577 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____67577  in
                    let uu____67592 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____67597 =
                        let uu____67600 =
                          let uu____67611 =
                            let uu____67614 =
                              let uu____67615 =
                                let uu____67626 =
                                  let uu____67635 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____67635  in
                                [uu____67626]  in
                              FStar_Syntax_Util.mk_app l_ite uu____67615  in
                            [uu____67614]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____67611
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____67600  in
                      FStar_Syntax_Util.ascribe uu____67597
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____67576 uu____67592
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____67679 = mk_lid "wp_if_then_else"  in
                    register env1 uu____67679 wp_if_then_else  in
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
                      let uu____67696 =
                        let uu____67707 =
                          let uu____67710 =
                            let uu____67711 =
                              let uu____67722 =
                                let uu____67725 =
                                  let uu____67726 =
                                    let uu____67737 =
                                      let uu____67746 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67746
                                       in
                                    [uu____67737]  in
                                  FStar_Syntax_Util.mk_app l_and uu____67726
                                   in
                                [uu____67725]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67722
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67711  in
                          let uu____67771 =
                            let uu____67774 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67774]  in
                          uu____67710 :: uu____67771  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67707
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67696  in
                    let uu____67783 =
                      let uu____67784 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67784  in
                    FStar_Syntax_Util.abs uu____67783 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____67800 = mk_lid "wp_assert"  in
                    register env1 uu____67800 wp_assert  in
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
                      let uu____67817 =
                        let uu____67828 =
                          let uu____67831 =
                            let uu____67832 =
                              let uu____67843 =
                                let uu____67846 =
                                  let uu____67847 =
                                    let uu____67858 =
                                      let uu____67867 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67867
                                       in
                                    [uu____67858]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____67847
                                   in
                                [uu____67846]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67843
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67832  in
                          let uu____67892 =
                            let uu____67895 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67895]  in
                          uu____67831 :: uu____67892  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67828
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67817  in
                    let uu____67904 =
                      let uu____67905 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67905  in
                    FStar_Syntax_Util.abs uu____67904 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____67921 = mk_lid "wp_assume"  in
                    register env1 uu____67921 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____67934 =
                        let uu____67943 =
                          let uu____67950 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____67950  in
                        [uu____67943]  in
                      let uu____67963 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____67934 uu____67963  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____67971 =
                        let uu____67982 =
                          let uu____67985 =
                            let uu____67986 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67986  in
                          let uu____68005 =
                            let uu____68008 =
                              let uu____68009 =
                                let uu____68020 =
                                  let uu____68023 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____68023]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____68020
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____68009
                               in
                            [uu____68008]  in
                          uu____67985 :: uu____68005  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67982
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67971  in
                    let uu____68040 =
                      let uu____68041 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____68041  in
                    FStar_Syntax_Util.abs uu____68040 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____68057 = mk_lid "wp_close"  in
                    register env1 uu____68057 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____68068 =
                      let uu____68069 =
                        let uu____68070 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____68070
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____68069
                       in
                    FStar_Pervasives_Native.Some uu____68068  in
                  let mk_forall1 x body =
                    let uu____68082 =
                      let uu____68089 =
                        let uu____68090 =
                          let uu____68107 =
                            let uu____68118 =
                              let uu____68127 =
                                let uu____68128 =
                                  let uu____68129 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____68129]  in
                                FStar_Syntax_Util.abs uu____68128 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____68127  in
                            [uu____68118]  in
                          (FStar_Syntax_Util.tforall, uu____68107)  in
                        FStar_Syntax_Syntax.Tm_app uu____68090  in
                      FStar_Syntax_Syntax.mk uu____68089  in
                    uu____68082 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____68190 =
                      let uu____68191 = FStar_Syntax_Subst.compress t  in
                      uu____68191.FStar_Syntax_Syntax.n  in
                    match uu____68190 with
                    | FStar_Syntax_Syntax.Tm_type uu____68195 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68228  ->
                              match uu____68228 with
                              | (b,uu____68237) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____68242 -> true  in
                  let rec is_monotonic t =
                    let uu____68255 =
                      let uu____68256 = FStar_Syntax_Subst.compress t  in
                      uu____68256.FStar_Syntax_Syntax.n  in
                    match uu____68255 with
                    | FStar_Syntax_Syntax.Tm_type uu____68260 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68293  ->
                              match uu____68293 with
                              | (b,uu____68302) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____68307 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____68381 =
                      let uu____68382 = FStar_Syntax_Subst.compress t1  in
                      uu____68382.FStar_Syntax_Syntax.n  in
                    match uu____68381 with
                    | FStar_Syntax_Syntax.Tm_type uu____68387 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____68390);
                                      FStar_Syntax_Syntax.pos = uu____68391;
                                      FStar_Syntax_Syntax.vars = uu____68392;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68436 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68436
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68446 =
                              let uu____68449 =
                                let uu____68460 =
                                  let uu____68469 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68469  in
                                [uu____68460]  in
                              FStar_Syntax_Util.mk_app x uu____68449  in
                            let uu____68486 =
                              let uu____68489 =
                                let uu____68500 =
                                  let uu____68509 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68509  in
                                [uu____68500]  in
                              FStar_Syntax_Util.mk_app y uu____68489  in
                            mk_rel1 b uu____68446 uu____68486  in
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
                             let uu____68533 =
                               let uu____68536 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68539 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68536 uu____68539  in
                             let uu____68542 =
                               let uu____68545 =
                                 let uu____68548 =
                                   let uu____68559 =
                                     let uu____68568 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68568
                                      in
                                   [uu____68559]  in
                                 FStar_Syntax_Util.mk_app x uu____68548  in
                               let uu____68585 =
                                 let uu____68588 =
                                   let uu____68599 =
                                     let uu____68608 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68608
                                      in
                                   [uu____68599]  in
                                 FStar_Syntax_Util.mk_app y uu____68588  in
                               mk_rel1 b uu____68545 uu____68585  in
                             FStar_Syntax_Util.mk_imp uu____68533 uu____68542
                              in
                           let uu____68625 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68625)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____68628);
                                      FStar_Syntax_Syntax.pos = uu____68629;
                                      FStar_Syntax_Syntax.vars = uu____68630;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68674 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68674
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68684 =
                              let uu____68687 =
                                let uu____68698 =
                                  let uu____68707 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68707  in
                                [uu____68698]  in
                              FStar_Syntax_Util.mk_app x uu____68687  in
                            let uu____68724 =
                              let uu____68727 =
                                let uu____68738 =
                                  let uu____68747 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68747  in
                                [uu____68738]  in
                              FStar_Syntax_Util.mk_app y uu____68727  in
                            mk_rel1 b uu____68684 uu____68724  in
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
                             let uu____68771 =
                               let uu____68774 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68777 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68774 uu____68777  in
                             let uu____68780 =
                               let uu____68783 =
                                 let uu____68786 =
                                   let uu____68797 =
                                     let uu____68806 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68806
                                      in
                                   [uu____68797]  in
                                 FStar_Syntax_Util.mk_app x uu____68786  in
                               let uu____68823 =
                                 let uu____68826 =
                                   let uu____68837 =
                                     let uu____68846 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68846
                                      in
                                   [uu____68837]  in
                                 FStar_Syntax_Util.mk_app y uu____68826  in
                               mk_rel1 b uu____68783 uu____68823  in
                             FStar_Syntax_Util.mk_imp uu____68771 uu____68780
                              in
                           let uu____68863 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68863)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_68902 = t1  in
                          let uu____68903 =
                            let uu____68904 =
                              let uu____68919 =
                                let uu____68922 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____68922  in
                              ([binder], uu____68919)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____68904  in
                          {
                            FStar_Syntax_Syntax.n = uu____68903;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_68902.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_68902.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____68945 ->
                        failwith "unhandled arrow"
                    | uu____68963 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____69000 =
                        let uu____69001 = FStar_Syntax_Subst.compress t1  in
                        uu____69001.FStar_Syntax_Syntax.n  in
                      match uu____69000 with
                      | FStar_Syntax_Syntax.Tm_type uu____69004 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____69031 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____69031
                          ->
                          let project i tuple =
                            let projector =
                              let uu____69052 =
                                let uu____69053 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____69053 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____69052
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____69083 =
                            let uu____69094 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____69112  ->
                                     match uu____69112 with
                                     | (t2,q) ->
                                         let uu____69132 = project i x  in
                                         let uu____69135 = project i y  in
                                         mk_stronger t2 uu____69132
                                           uu____69135) args
                               in
                            match uu____69094 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____69083 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____69189);
                                      FStar_Syntax_Syntax.pos = uu____69190;
                                      FStar_Syntax_Syntax.vars = uu____69191;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69235  ->
                                   match uu____69235 with
                                   | (bv,q) ->
                                       let uu____69249 =
                                         let uu____69251 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69251  in
                                       FStar_Syntax_Syntax.gen_bv uu____69249
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69260 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69260) bvs
                             in
                          let body =
                            let uu____69262 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69265 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69262 uu____69265  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____69274);
                                      FStar_Syntax_Syntax.pos = uu____69275;
                                      FStar_Syntax_Syntax.vars = uu____69276;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69320  ->
                                   match uu____69320 with
                                   | (bv,q) ->
                                       let uu____69334 =
                                         let uu____69336 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69336  in
                                       FStar_Syntax_Syntax.gen_bv uu____69334
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69345 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69345) bvs
                             in
                          let body =
                            let uu____69347 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69350 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69347 uu____69350  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____69357 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____69360 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____69363 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____69366 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____69360 uu____69363 uu____69366  in
                    let uu____69369 =
                      let uu____69370 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____69370  in
                    FStar_Syntax_Util.abs uu____69369 body ret_tot_type  in
                  let stronger1 =
                    let uu____69412 = mk_lid "stronger"  in
                    register env1 uu____69412 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69420 = FStar_Util.prefix gamma  in
                    match uu____69420 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____69486 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____69486
                             in
                          let uu____69491 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____69491 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____69501 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____69501  in
                              let guard_free1 =
                                let uu____69513 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____69513  in
                              let pat =
                                let uu____69517 =
                                  let uu____69528 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____69528]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____69517
                                 in
                              let pattern_guarded_body =
                                let uu____69556 =
                                  let uu____69557 =
                                    let uu____69564 =
                                      let uu____69565 =
                                        let uu____69578 =
                                          let uu____69589 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____69589]  in
                                        [uu____69578]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____69565
                                       in
                                    (body, uu____69564)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____69557  in
                                mk1 uu____69556  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____69636 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____69645 =
                            let uu____69648 =
                              let uu____69649 =
                                let uu____69652 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____69655 =
                                  let uu____69666 = args_of_binders1 wp_args
                                     in
                                  let uu____69669 =
                                    let uu____69672 =
                                      let uu____69673 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____69673
                                       in
                                    [uu____69672]  in
                                  FStar_List.append uu____69666 uu____69669
                                   in
                                FStar_Syntax_Util.mk_app uu____69652
                                  uu____69655
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____69649  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____69648
                             in
                          FStar_Syntax_Util.abs gamma uu____69645
                            ret_gtot_type
                           in
                        let uu____69674 =
                          let uu____69675 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____69675  in
                        FStar_Syntax_Util.abs uu____69674 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____69691 = mk_lid "ite_wp"  in
                    register env1 uu____69691 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69699 = FStar_Util.prefix gamma  in
                    match uu____69699 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____69757 =
                            let uu____69758 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____69765 =
                              let uu____69776 =
                                let uu____69785 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____69785  in
                              [uu____69776]  in
                            FStar_Syntax_Util.mk_app uu____69758 uu____69765
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____69757
                           in
                        let uu____69802 =
                          let uu____69803 =
                            let uu____69812 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____69812 gamma  in
                          FStar_List.append binders uu____69803  in
                        FStar_Syntax_Util.abs uu____69802 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____69834 = mk_lid "null_wp"  in
                    register env1 uu____69834 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____69847 =
                        let uu____69858 =
                          let uu____69861 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____69862 =
                            let uu____69865 =
                              let uu____69866 =
                                let uu____69877 =
                                  let uu____69886 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____69886  in
                                [uu____69877]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____69866
                               in
                            let uu____69903 =
                              let uu____69906 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____69906]  in
                            uu____69865 :: uu____69903  in
                          uu____69861 :: uu____69862  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____69858
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____69847  in
                    let uu____69915 =
                      let uu____69916 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____69916  in
                    FStar_Syntax_Util.abs uu____69915 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____69932 = mk_lid "wp_trivial"  in
                    register env1 uu____69932 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____69938 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____69938
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____69950 =
                      let uu____69951 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____69951  in
                    let uu____69999 =
                      let uu___934_70000 = ed  in
                      let uu____70001 =
                        let uu____70002 = c wp_if_then_else2  in
                        ([], uu____70002)  in
                      let uu____70009 =
                        let uu____70010 = c ite_wp2  in ([], uu____70010)  in
                      let uu____70017 =
                        let uu____70018 = c stronger2  in ([], uu____70018)
                         in
                      let uu____70025 =
                        let uu____70026 = c wp_close2  in ([], uu____70026)
                         in
                      let uu____70033 =
                        let uu____70034 = c wp_assert2  in ([], uu____70034)
                         in
                      let uu____70041 =
                        let uu____70042 = c wp_assume2  in ([], uu____70042)
                         in
                      let uu____70049 =
                        let uu____70050 = c null_wp2  in ([], uu____70050)
                         in
                      let uu____70057 =
                        let uu____70058 = c wp_trivial2  in ([], uu____70058)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_70000.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_70000.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_70000.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_70000.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_70000.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_70000.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_70000.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____70001;
                        FStar_Syntax_Syntax.ite_wp = uu____70009;
                        FStar_Syntax_Syntax.stronger = uu____70017;
                        FStar_Syntax_Syntax.close_wp = uu____70025;
                        FStar_Syntax_Syntax.assert_p = uu____70033;
                        FStar_Syntax_Syntax.assume_p = uu____70041;
                        FStar_Syntax_Syntax.null_wp = uu____70049;
                        FStar_Syntax_Syntax.trivial = uu____70057;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_70000.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_70000.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_70000.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_70000.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_70000.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____69950, uu____69999)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_70082 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_70082.subst);
        tc_const = (uu___939_70082.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____70103 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____70123 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____70144) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_70158  ->
                match uu___585_70158 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____70161 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____70163 ->
        let uu____70164 =
          let uu____70170 =
            let uu____70172 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____70172
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____70170)  in
        FStar_Errors.raise_error uu____70164 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_70182  ->
    match uu___586_70182 with
    | N t ->
        let uu____70185 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____70185
    | M t ->
        let uu____70189 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____70189
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____70198,c) -> nm_of_comp c
    | uu____70220 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____70233 = nm_of_comp c  in
    match uu____70233 with | M uu____70235 -> true | N uu____70237 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____70248 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____70264 =
        let uu____70273 =
          let uu____70280 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____70280  in
        [uu____70273]  in
      let uu____70299 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____70264 uu____70299  in
    let uu____70302 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____70302
  
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
        let uu____70344 =
          let uu____70345 =
            let uu____70360 =
              let uu____70369 =
                let uu____70376 =
                  let uu____70377 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____70377  in
                let uu____70378 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____70376, uu____70378)  in
              [uu____70369]  in
            let uu____70396 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____70360, uu____70396)  in
          FStar_Syntax_Syntax.Tm_arrow uu____70345  in
        mk1 uu____70344

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70436) ->
          let binders1 =
            FStar_List.map
              (fun uu____70482  ->
                 match uu____70482 with
                 | (bv,aqual) ->
                     let uu____70501 =
                       let uu___989_70502 = bv  in
                       let uu____70503 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_70502.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_70502.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____70503
                       }  in
                     (uu____70501, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____70508,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____70510);
                              FStar_Syntax_Syntax.pos = uu____70511;
                              FStar_Syntax_Syntax.vars = uu____70512;_})
               ->
               let uu____70541 =
                 let uu____70542 =
                   let uu____70557 =
                     let uu____70560 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____70560  in
                   (binders1, uu____70557)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____70542  in
               mk1 uu____70541
           | uu____70571 ->
               let uu____70572 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____70572 with
                | N hn ->
                    let uu____70574 =
                      let uu____70575 =
                        let uu____70590 =
                          let uu____70593 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____70593  in
                        (binders1, uu____70590)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70575  in
                    mk1 uu____70574
                | M a ->
                    let uu____70605 =
                      let uu____70606 =
                        let uu____70621 =
                          let uu____70630 =
                            let uu____70639 =
                              let uu____70646 =
                                let uu____70647 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____70647  in
                              let uu____70648 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____70646, uu____70648)  in
                            [uu____70639]  in
                          FStar_List.append binders1 uu____70630  in
                        let uu____70672 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____70621, uu____70672)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70606  in
                    mk1 uu____70605))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____70766 = f x  in
                    FStar_Util.string_builder_append strb uu____70766);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____70775 = f x1  in
                         FStar_Util.string_builder_append strb uu____70775))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____70779 =
              let uu____70785 =
                let uu____70787 = FStar_Syntax_Print.term_to_string t2  in
                let uu____70789 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____70787 uu____70789
                 in
              (FStar_Errors.Warning_DependencyFound, uu____70785)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____70779  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____70811 =
              let uu____70812 = FStar_Syntax_Subst.compress ty  in
              uu____70812.FStar_Syntax_Syntax.n  in
            match uu____70811 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____70838 =
                  let uu____70840 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____70840  in
                if uu____70838
                then false
                else
                  (try
                     (fun uu___1038_70857  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____70881 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____70881 s  in
                              let uu____70884 =
                                let uu____70886 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____70886  in
                              if uu____70884
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____70892 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____70892 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____70917  ->
                                          match uu____70917 with
                                          | (bv,uu____70929) ->
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
            | uu____70957 ->
                ((let uu____70959 =
                    let uu____70965 =
                      let uu____70967 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____70967
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____70965)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____70959);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____70983 =
              let uu____70984 = FStar_Syntax_Subst.compress head2  in
              uu____70984.FStar_Syntax_Syntax.n  in
            match uu____70983 with
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
                  (let uu____70990 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____70990)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____70993 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____70993 with
                 | ((uu____71003,ty),uu____71005) ->
                     let uu____71010 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____71010
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____71023 =
                         let uu____71024 = FStar_Syntax_Subst.compress res
                            in
                         uu____71024.FStar_Syntax_Syntax.n  in
                       (match uu____71023 with
                        | FStar_Syntax_Syntax.Tm_app uu____71028 -> true
                        | uu____71046 ->
                            ((let uu____71048 =
                                let uu____71054 =
                                  let uu____71056 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____71056
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____71054)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____71048);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____71064 -> true
            | FStar_Syntax_Syntax.Tm_name uu____71066 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71069) ->
                is_valid_application t2
            | uu____71074 -> false  in
          let uu____71076 = is_valid_application head1  in
          if uu____71076
          then
            let uu____71079 =
              let uu____71080 =
                let uu____71097 =
                  FStar_List.map
                    (fun uu____71126  ->
                       match uu____71126 with
                       | (t2,qual) ->
                           let uu____71151 = star_type' env t2  in
                           (uu____71151, qual)) args
                   in
                (head1, uu____71097)  in
              FStar_Syntax_Syntax.Tm_app uu____71080  in
            mk1 uu____71079
          else
            (let uu____71168 =
               let uu____71174 =
                 let uu____71176 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____71176
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____71174)  in
             FStar_Errors.raise_err uu____71168)
      | FStar_Syntax_Syntax.Tm_bvar uu____71180 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____71181 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____71182 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____71183 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____71211 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____71211 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_71219 = env  in
                 let uu____71220 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____71220;
                   subst = (uu___1110_71219.subst);
                   tc_const = (uu___1110_71219.tc_const)
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
               ((let uu___1125_71247 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_71247.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_71247.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____71254 =
            let uu____71255 =
              let uu____71262 = star_type' env t2  in (uu____71262, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____71255  in
          mk1 uu____71254
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____71314 =
            let uu____71315 =
              let uu____71342 = star_type' env e  in
              let uu____71345 =
                let uu____71362 =
                  let uu____71371 = star_type' env t2  in
                  FStar_Util.Inl uu____71371  in
                (uu____71362, FStar_Pervasives_Native.None)  in
              (uu____71342, uu____71345, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71315  in
          mk1 uu____71314
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____71459 =
            let uu____71460 =
              let uu____71487 = star_type' env e  in
              let uu____71490 =
                let uu____71507 =
                  let uu____71516 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____71516  in
                (uu____71507, FStar_Pervasives_Native.None)  in
              (uu____71487, uu____71490, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71460  in
          mk1 uu____71459
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____71557,(uu____71558,FStar_Pervasives_Native.Some uu____71559),uu____71560)
          ->
          let uu____71609 =
            let uu____71615 =
              let uu____71617 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____71617
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71615)  in
          FStar_Errors.raise_err uu____71609
      | FStar_Syntax_Syntax.Tm_refine uu____71621 ->
          let uu____71628 =
            let uu____71634 =
              let uu____71636 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____71636
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71634)  in
          FStar_Errors.raise_err uu____71628
      | FStar_Syntax_Syntax.Tm_uinst uu____71640 ->
          let uu____71647 =
            let uu____71653 =
              let uu____71655 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____71655
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71653)  in
          FStar_Errors.raise_err uu____71647
      | FStar_Syntax_Syntax.Tm_quoted uu____71659 ->
          let uu____71666 =
            let uu____71672 =
              let uu____71674 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____71674
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71672)  in
          FStar_Errors.raise_err uu____71666
      | FStar_Syntax_Syntax.Tm_constant uu____71678 ->
          let uu____71679 =
            let uu____71685 =
              let uu____71687 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____71687
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71685)  in
          FStar_Errors.raise_err uu____71679
      | FStar_Syntax_Syntax.Tm_match uu____71691 ->
          let uu____71714 =
            let uu____71720 =
              let uu____71722 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____71722
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71720)  in
          FStar_Errors.raise_err uu____71714
      | FStar_Syntax_Syntax.Tm_let uu____71726 ->
          let uu____71740 =
            let uu____71746 =
              let uu____71748 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____71748
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71746)  in
          FStar_Errors.raise_err uu____71740
      | FStar_Syntax_Syntax.Tm_uvar uu____71752 ->
          let uu____71765 =
            let uu____71771 =
              let uu____71773 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____71773
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71771)  in
          FStar_Errors.raise_err uu____71765
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71777 =
            let uu____71783 =
              let uu____71785 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____71785
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71783)  in
          FStar_Errors.raise_err uu____71777
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71790 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____71790
      | FStar_Syntax_Syntax.Tm_delayed uu____71793 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_71825  ->
    match uu___588_71825 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_71836  ->
                match uu___587_71836 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____71839 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____71849 =
      let uu____71850 = FStar_Syntax_Subst.compress t  in
      uu____71850.FStar_Syntax_Syntax.n  in
    match uu____71849 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____71882 =
            let uu____71883 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____71883  in
          is_C uu____71882  in
        if r
        then
          ((let uu____71907 =
              let uu____71909 =
                FStar_List.for_all
                  (fun uu____71920  ->
                     match uu____71920 with | (h,uu____71929) -> is_C h) args
                 in
              Prims.op_Negation uu____71909  in
            if uu____71907 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____71942 =
              let uu____71944 =
                FStar_List.for_all
                  (fun uu____71956  ->
                     match uu____71956 with
                     | (h,uu____71965) ->
                         let uu____71970 = is_C h  in
                         Prims.op_Negation uu____71970) args
                 in
              Prims.op_Negation uu____71944  in
            if uu____71942 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____71999 = nm_of_comp comp  in
        (match uu____71999 with
         | M t1 ->
             ((let uu____72003 = is_C t1  in
               if uu____72003 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____72012) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____72018) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____72024,uu____72025) -> is_C t1
    | uu____72066 -> false
  
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
          let uu____72102 =
            let uu____72103 =
              let uu____72120 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____72123 =
                let uu____72134 =
                  let uu____72143 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____72143)  in
                [uu____72134]  in
              (uu____72120, uu____72123)  in
            FStar_Syntax_Syntax.Tm_app uu____72103  in
          mk1 uu____72102  in
        let uu____72179 =
          let uu____72180 = FStar_Syntax_Syntax.mk_binder p  in [uu____72180]
           in
        FStar_Syntax_Util.abs uu____72179 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_72205  ->
    match uu___589_72205 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____72208 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____72446 =
          match uu____72446 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____72483 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____72486 =
                       let uu____72488 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____72488  in
                     Prims.op_Negation uu____72486)
                   in
                if uu____72483
                then
                  let uu____72490 =
                    let uu____72496 =
                      let uu____72498 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____72500 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____72502 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____72498 uu____72500 uu____72502
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____72496)  in
                  FStar_Errors.raise_err uu____72490
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____72527 = mk_return env t1 s_e  in
                     ((M t1), uu____72527, u_e)))
               | (M t1,N t2) ->
                   let uu____72534 =
                     let uu____72540 =
                       let uu____72542 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____72544 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____72546 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____72542 uu____72544 uu____72546
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____72540)
                      in
                   FStar_Errors.raise_err uu____72534)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_72598 =
            match uu___590_72598 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____72614 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____72635 =
                let uu____72641 =
                  let uu____72643 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____72643
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____72641)  in
              FStar_Errors.raise_error uu____72635 e2.FStar_Syntax_Syntax.pos
          | M uu____72653 ->
              let uu____72654 = check env1 e2 context_nm  in
              strip_m uu____72654
           in
        let uu____72661 =
          let uu____72662 = FStar_Syntax_Subst.compress e  in
          uu____72662.FStar_Syntax_Syntax.n  in
        match uu____72661 with
        | FStar_Syntax_Syntax.Tm_bvar uu____72671 ->
            let uu____72672 = infer env e  in return_if uu____72672
        | FStar_Syntax_Syntax.Tm_name uu____72679 ->
            let uu____72680 = infer env e  in return_if uu____72680
        | FStar_Syntax_Syntax.Tm_fvar uu____72687 ->
            let uu____72688 = infer env e  in return_if uu____72688
        | FStar_Syntax_Syntax.Tm_abs uu____72695 ->
            let uu____72714 = infer env e  in return_if uu____72714
        | FStar_Syntax_Syntax.Tm_constant uu____72721 ->
            let uu____72722 = infer env e  in return_if uu____72722
        | FStar_Syntax_Syntax.Tm_quoted uu____72729 ->
            let uu____72736 = infer env e  in return_if uu____72736
        | FStar_Syntax_Syntax.Tm_app uu____72743 ->
            let uu____72760 = infer env e  in return_if uu____72760
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____72768 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____72768 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____72833) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____72839) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____72845,uu____72846) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____72887 ->
            let uu____72901 =
              let uu____72903 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____72903  in
            failwith uu____72901
        | FStar_Syntax_Syntax.Tm_type uu____72912 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____72920 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____72942 ->
            let uu____72949 =
              let uu____72951 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____72951  in
            failwith uu____72949
        | FStar_Syntax_Syntax.Tm_uvar uu____72960 ->
            let uu____72973 =
              let uu____72975 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____72975  in
            failwith uu____72973
        | FStar_Syntax_Syntax.Tm_delayed uu____72984 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____73014 =
              let uu____73016 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____73016  in
            failwith uu____73014

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
      let uu____73046 =
        let uu____73047 = FStar_Syntax_Subst.compress e  in
        uu____73047.FStar_Syntax_Syntax.n  in
      match uu____73046 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____73066 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____73066
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____73117;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____73118;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____73124 =
                  let uu___1360_73125 = rc  in
                  let uu____73126 =
                    let uu____73131 =
                      let uu____73134 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____73134  in
                    FStar_Pervasives_Native.Some uu____73131  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_73125.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____73126;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_73125.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____73124
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_73146 = env  in
            let uu____73147 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____73147;
              subst = (uu___1366_73146.subst);
              tc_const = (uu___1366_73146.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____73173  ->
                 match uu____73173 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_73196 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_73196.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_73196.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____73197 =
            FStar_List.fold_left
              (fun uu____73228  ->
                 fun uu____73229  ->
                   match (uu____73228, uu____73229) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____73287 = is_C c  in
                       if uu____73287
                       then
                         let xw =
                           let uu____73297 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____73297
                            in
                         let x =
                           let uu___1385_73300 = bv  in
                           let uu____73301 =
                             let uu____73304 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____73304  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_73300.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_73300.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____73301
                           }  in
                         let env3 =
                           let uu___1388_73306 = env2  in
                           let uu____73307 =
                             let uu____73310 =
                               let uu____73311 =
                                 let uu____73318 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____73318)  in
                               FStar_Syntax_Syntax.NT uu____73311  in
                             uu____73310 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_73306.tcenv);
                             subst = uu____73307;
                             tc_const = (uu___1388_73306.tc_const)
                           }  in
                         let uu____73323 =
                           let uu____73326 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____73327 =
                             let uu____73330 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____73330 :: acc  in
                           uu____73326 :: uu____73327  in
                         (env3, uu____73323)
                       else
                         (let x =
                            let uu___1391_73336 = bv  in
                            let uu____73337 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_73336.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_73336.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____73337
                            }  in
                          let uu____73340 =
                            let uu____73343 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____73343 :: acc  in
                          (env2, uu____73340))) (env1, []) binders1
             in
          (match uu____73197 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____73363 =
                 let check_what =
                   let uu____73389 = is_monadic rc_opt1  in
                   if uu____73389 then check_m else check_n  in
                 let uu____73406 = check_what env2 body1  in
                 match uu____73406 with
                 | (t,s_body,u_body) ->
                     let uu____73426 =
                       let uu____73429 =
                         let uu____73430 = is_monadic rc_opt1  in
                         if uu____73430 then M t else N t  in
                       comp_of_nm uu____73429  in
                     (uu____73426, s_body, u_body)
                  in
               (match uu____73363 with
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
                                 let uu____73470 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_73476  ->
                                           match uu___591_73476 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____73479 -> false))
                                    in
                                 if uu____73470
                                 then
                                   let uu____73482 =
                                     FStar_List.filter
                                       (fun uu___592_73486  ->
                                          match uu___592_73486 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____73489 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____73482
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____73500 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_73506  ->
                                         match uu___593_73506 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____73509 -> false))
                                  in
                               if uu____73500
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_73518  ->
                                        match uu___594_73518 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____73521 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____73523 =
                                   let uu____73524 =
                                     let uu____73529 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____73529
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____73524 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____73523
                               else
                                 (let uu____73536 =
                                    let uu___1432_73537 = rc  in
                                    let uu____73538 =
                                      let uu____73543 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____73543
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_73537.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____73538;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_73537.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____73536))
                       in
                    let uu____73548 =
                      let comp1 =
                        let uu____73556 = is_monadic rc_opt1  in
                        let uu____73558 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____73556 uu____73558
                         in
                      let uu____73559 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____73559,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____73548 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____73597 =
                             let uu____73598 =
                               let uu____73617 =
                                 let uu____73620 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____73620 s_rc_opt  in
                               (s_binders1, s_body1, uu____73617)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73598  in
                           mk1 uu____73597  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____73640 =
                             let uu____73641 =
                               let uu____73660 =
                                 let uu____73663 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____73663 u_rc_opt  in
                               (u_binders2, u_body2, uu____73660)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73641  in
                           mk1 uu____73640  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____73679;_};
            FStar_Syntax_Syntax.fv_delta = uu____73680;
            FStar_Syntax_Syntax.fv_qual = uu____73681;_}
          ->
          let uu____73684 =
            let uu____73689 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____73689  in
          (match uu____73684 with
           | (uu____73720,t) ->
               let uu____73722 =
                 let uu____73723 = normalize1 t  in N uu____73723  in
               (uu____73722, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____73724;
             FStar_Syntax_Syntax.vars = uu____73725;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73804 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73804 with
           | (unary_op1,uu____73828) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____73899;
             FStar_Syntax_Syntax.vars = uu____73900;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73996 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73996 with
           | (unary_op1,uu____74020) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74099;
             FStar_Syntax_Syntax.vars = uu____74100;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____74138 = infer env a  in
          (match uu____74138 with
           | (t,s,u) ->
               let uu____74154 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74154 with
                | (head1,uu____74178) ->
                    let uu____74203 =
                      let uu____74204 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____74204  in
                    let uu____74205 =
                      let uu____74206 =
                        let uu____74207 =
                          let uu____74224 =
                            let uu____74235 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74235]  in
                          (head1, uu____74224)  in
                        FStar_Syntax_Syntax.Tm_app uu____74207  in
                      mk1 uu____74206  in
                    let uu____74272 =
                      let uu____74273 =
                        let uu____74274 =
                          let uu____74291 =
                            let uu____74302 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74302]  in
                          (head1, uu____74291)  in
                        FStar_Syntax_Syntax.Tm_app uu____74274  in
                      mk1 uu____74273  in
                    (uu____74203, uu____74205, uu____74272)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74339;
             FStar_Syntax_Syntax.vars = uu____74340;_},(a1,uu____74342)::a2::[])
          ->
          let uu____74398 = infer env a1  in
          (match uu____74398 with
           | (t,s,u) ->
               let uu____74414 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74414 with
                | (head1,uu____74438) ->
                    let uu____74463 =
                      let uu____74464 =
                        let uu____74465 =
                          let uu____74482 =
                            let uu____74493 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74493; a2]  in
                          (head1, uu____74482)  in
                        FStar_Syntax_Syntax.Tm_app uu____74465  in
                      mk1 uu____74464  in
                    let uu____74538 =
                      let uu____74539 =
                        let uu____74540 =
                          let uu____74557 =
                            let uu____74568 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74568; a2]  in
                          (head1, uu____74557)  in
                        FStar_Syntax_Syntax.Tm_app uu____74540  in
                      mk1 uu____74539  in
                    (t, uu____74463, uu____74538)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74613;
             FStar_Syntax_Syntax.vars = uu____74614;_},uu____74615)
          ->
          let uu____74640 =
            let uu____74646 =
              let uu____74648 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74648
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74646)  in
          FStar_Errors.raise_error uu____74640 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74658;
             FStar_Syntax_Syntax.vars = uu____74659;_},uu____74660)
          ->
          let uu____74685 =
            let uu____74691 =
              let uu____74693 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74693
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74691)  in
          FStar_Errors.raise_error uu____74685 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____74729 = check_n env head1  in
          (match uu____74729 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____74752 =
                   let uu____74753 = FStar_Syntax_Subst.compress t  in
                   uu____74753.FStar_Syntax_Syntax.n  in
                 match uu____74752 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____74757 -> true
                 | uu____74773 -> false  in
               let rec flatten1 t =
                 let uu____74795 =
                   let uu____74796 = FStar_Syntax_Subst.compress t  in
                   uu____74796.FStar_Syntax_Syntax.n  in
                 match uu____74795 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____74815);
                                FStar_Syntax_Syntax.pos = uu____74816;
                                FStar_Syntax_Syntax.vars = uu____74817;_})
                     when is_arrow t1 ->
                     let uu____74846 = flatten1 t1  in
                     (match uu____74846 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____74946,uu____74947) -> flatten1 e1
                 | uu____74988 ->
                     let uu____74989 =
                       let uu____74995 =
                         let uu____74997 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____74997
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____74995)  in
                     FStar_Errors.raise_err uu____74989
                  in
               let uu____75015 = flatten1 t_head  in
               (match uu____75015 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____75090 =
                          let uu____75096 =
                            let uu____75098 = FStar_Util.string_of_int n1  in
                            let uu____75106 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____75118 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____75098 uu____75106 uu____75118
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____75096)
                           in
                        FStar_Errors.raise_err uu____75090)
                     else ();
                     (let uu____75130 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____75130 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____75183 args1 =
                            match uu____75183 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____75283 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____75283
                                 | (binders3,[]) ->
                                     let uu____75321 =
                                       let uu____75322 =
                                         let uu____75325 =
                                           let uu____75326 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____75326
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____75325
                                          in
                                       uu____75322.FStar_Syntax_Syntax.n  in
                                     (match uu____75321 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____75359 =
                                            let uu____75360 =
                                              let uu____75361 =
                                                let uu____75376 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____75376)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____75361
                                               in
                                            mk1 uu____75360  in
                                          N uu____75359
                                      | uu____75389 -> failwith "wat?")
                                 | ([],uu____75391::uu____75392) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____75445)::binders3,(arg,uu____75448)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____75535 = FStar_List.splitAt n' binders1
                             in
                          (match uu____75535 with
                           | (binders2,uu____75573) ->
                               let uu____75606 =
                                 let uu____75629 =
                                   FStar_List.map2
                                     (fun uu____75691  ->
                                        fun uu____75692  ->
                                          match (uu____75691, uu____75692)
                                          with
                                          | ((bv,uu____75740),(arg,q)) ->
                                              let uu____75769 =
                                                let uu____75770 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____75770.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____75769 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____75791 ->
                                                   let uu____75792 =
                                                     let uu____75799 =
                                                       star_type' env arg  in
                                                     (uu____75799, q)  in
                                                   (uu____75792, [(arg, q)])
                                               | uu____75836 ->
                                                   let uu____75837 =
                                                     check_n env arg  in
                                                   (match uu____75837 with
                                                    | (uu____75862,s_arg,u_arg)
                                                        ->
                                                        let uu____75865 =
                                                          let uu____75874 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____75874
                                                          then
                                                            let uu____75885 =
                                                              let uu____75892
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____75892,
                                                                q)
                                                               in
                                                            [uu____75885;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____75865))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____75629  in
                               (match uu____75606 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____76020 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____76033 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____76020, uu____76033)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____76102) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____76108) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____76114,uu____76115) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____76157 =
            let uu____76158 = env.tc_const c  in N uu____76158  in
          (uu____76157, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____76165 ->
          let uu____76179 =
            let uu____76181 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____76181  in
          failwith uu____76179
      | FStar_Syntax_Syntax.Tm_type uu____76190 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____76198 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____76220 ->
          let uu____76227 =
            let uu____76229 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____76229  in
          failwith uu____76227
      | FStar_Syntax_Syntax.Tm_uvar uu____76238 ->
          let uu____76251 =
            let uu____76253 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____76253  in
          failwith uu____76251
      | FStar_Syntax_Syntax.Tm_delayed uu____76262 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____76292 =
            let uu____76294 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____76294  in
          failwith uu____76292

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
          let uu____76343 = check_n env e0  in
          match uu____76343 with
          | (uu____76356,s_e0,u_e0) ->
              let uu____76359 =
                let uu____76388 =
                  FStar_List.map
                    (fun b  ->
                       let uu____76449 = FStar_Syntax_Subst.open_branch b  in
                       match uu____76449 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_76491 = env  in
                             let uu____76492 =
                               let uu____76493 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____76493
                                in
                             {
                               tcenv = uu____76492;
                               subst = (uu___1707_76491.subst);
                               tc_const = (uu___1707_76491.tc_const)
                             }  in
                           let uu____76496 = f env1 body  in
                           (match uu____76496 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____76568 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____76388  in
              (match uu____76359 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____76674 = FStar_List.hd nms  in
                     match uu____76674 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_76683  ->
                          match uu___595_76683 with
                          | M uu____76685 -> true
                          | uu____76687 -> false) nms
                      in
                   let uu____76689 =
                     let uu____76726 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____76816  ->
                              match uu____76816 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____77000 =
                                         check env original_body (M t2)  in
                                       (match uu____77000 with
                                        | (uu____77037,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____77076,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____76726  in
                   (match uu____76689 with
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
                              (fun uu____77265  ->
                                 match uu____77265 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____77316 =
                                         let uu____77317 =
                                           let uu____77334 =
                                             let uu____77345 =
                                               let uu____77354 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____77357 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____77354, uu____77357)  in
                                             [uu____77345]  in
                                           (s_body, uu____77334)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____77317
                                          in
                                       mk1 uu____77316  in
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
                            let uu____77492 =
                              let uu____77493 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____77493]  in
                            let uu____77512 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____77492 uu____77512
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____77536 =
                              let uu____77545 =
                                let uu____77552 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____77552
                                 in
                              [uu____77545]  in
                            let uu____77571 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____77536 uu____77571
                             in
                          let uu____77574 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____77613 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____77574, uu____77613)
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
                           let uu____77723 =
                             let uu____77724 =
                               let uu____77725 =
                                 let uu____77752 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____77752,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____77725
                                in
                             mk1 uu____77724  in
                           let uu____77811 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____77723, uu____77811))))

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
              let uu____77876 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____77876]  in
            let uu____77895 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____77895 with
            | (x_binders1,e21) ->
                let uu____77908 = infer env e1  in
                (match uu____77908 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____77925 = is_C t1  in
                       if uu____77925
                       then
                         let uu___1793_77928 = binding  in
                         let uu____77929 =
                           let uu____77932 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____77932  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_77928.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_77928.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____77929;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_77928.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_77928.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_77928.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_77928.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_77936 = env  in
                       let uu____77937 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_77939 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_77939.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_77939.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____77937;
                         subst = (uu___1796_77936.subst);
                         tc_const = (uu___1796_77936.tc_const)
                       }  in
                     let uu____77940 = proceed env1 e21  in
                     (match uu____77940 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_77957 = binding  in
                            let uu____77958 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_77957.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_77957.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____77958;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_77957.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_77957.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_77957.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_77957.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____77961 =
                            let uu____77962 =
                              let uu____77963 =
                                let uu____77977 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_77994 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_77994.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_77994.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_77994.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_77994.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_77994.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_77994.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____77977)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77963  in
                            mk1 uu____77962  in
                          let uu____77995 =
                            let uu____77996 =
                              let uu____77997 =
                                let uu____78011 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_78028 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_78028.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_78028.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_78028.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_78028.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_78028.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_78028.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78011)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77997  in
                            mk1 uu____77996  in
                          (nm_rec, uu____77961, uu____77995))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_78033 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_78033.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_78033.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_78033.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_78033.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_78033.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_78035 = env  in
                       let uu____78036 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_78038 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_78038.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_78038.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____78036;
                         subst = (uu___1820_78035.subst);
                         tc_const = (uu___1820_78035.tc_const)
                       }  in
                     let uu____78039 = ensure_m env1 e21  in
                     (match uu____78039 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____78063 =
                              let uu____78064 =
                                let uu____78081 =
                                  let uu____78092 =
                                    let uu____78101 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____78104 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78101, uu____78104)  in
                                  [uu____78092]  in
                                (s_e2, uu____78081)  in
                              FStar_Syntax_Syntax.Tm_app uu____78064  in
                            mk1 uu____78063  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____78146 =
                              let uu____78147 =
                                let uu____78164 =
                                  let uu____78175 =
                                    let uu____78184 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____78184)  in
                                  [uu____78175]  in
                                (s_e1, uu____78164)  in
                              FStar_Syntax_Syntax.Tm_app uu____78147  in
                            mk1 uu____78146  in
                          let uu____78220 =
                            let uu____78221 =
                              let uu____78222 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____78222]  in
                            FStar_Syntax_Util.abs uu____78221 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____78241 =
                            let uu____78242 =
                              let uu____78243 =
                                let uu____78257 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_78274 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_78274.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_78274.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_78274.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_78274.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_78274.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_78274.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78257)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78243  in
                            mk1 uu____78242  in
                          ((M t2), uu____78220, uu____78241)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78284 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____78284  in
      let uu____78285 = check env e mn  in
      match uu____78285 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78301 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78324 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____78324  in
      let uu____78325 = check env e mn  in
      match uu____78325 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78341 -> failwith "[check_m]: impossible"

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
        (let uu____78374 =
           let uu____78376 = is_C c  in Prims.op_Negation uu____78376  in
         if uu____78374 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____78390 =
           let uu____78391 = FStar_Syntax_Subst.compress c  in
           uu____78391.FStar_Syntax_Syntax.n  in
         match uu____78390 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____78420 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____78420 with
              | (wp_head,wp_args) ->
                  ((let uu____78464 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____78483 =
                           let uu____78485 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____78485
                            in
                         Prims.op_Negation uu____78483)
                       in
                    if uu____78464 then failwith "mismatch" else ());
                   (let uu____78498 =
                      let uu____78499 =
                        let uu____78516 =
                          FStar_List.map2
                            (fun uu____78554  ->
                               fun uu____78555  ->
                                 match (uu____78554, uu____78555) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____78617 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____78617
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____78626 =
                                         let uu____78628 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____78628 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____78626
                                       then
                                         let uu____78630 =
                                           let uu____78636 =
                                             let uu____78638 =
                                               print_implicit q  in
                                             let uu____78640 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____78638 uu____78640
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____78636)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____78630
                                       else ());
                                      (let uu____78646 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____78646, q)))) args wp_args
                           in
                        (head1, uu____78516)  in
                      FStar_Syntax_Syntax.Tm_app uu____78499  in
                    mk1 uu____78498)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____78692 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____78692 with
              | (binders_orig,comp1) ->
                  let uu____78699 =
                    let uu____78716 =
                      FStar_List.map
                        (fun uu____78756  ->
                           match uu____78756 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____78784 = is_C h  in
                               if uu____78784
                               then
                                 let w' =
                                   let uu____78800 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____78800
                                    in
                                 let uu____78802 =
                                   let uu____78811 =
                                     let uu____78820 =
                                       let uu____78827 =
                                         let uu____78828 =
                                           let uu____78829 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____78829  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____78828
                                          in
                                       (uu____78827, q)  in
                                     [uu____78820]  in
                                   (w', q) :: uu____78811  in
                                 (w', uu____78802)
                               else
                                 (let x =
                                    let uu____78863 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____78863
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____78716  in
                  (match uu____78699 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____78937 =
                           let uu____78940 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____78940
                            in
                         FStar_Syntax_Subst.subst_comp uu____78937 comp1  in
                       let app =
                         let uu____78944 =
                           let uu____78945 =
                             let uu____78962 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____78981 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____78982 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78981, uu____78982)) bvs
                                in
                             (wp, uu____78962)  in
                           FStar_Syntax_Syntax.Tm_app uu____78945  in
                         mk1 uu____78944  in
                       let comp3 =
                         let uu____78997 = type_of_comp comp2  in
                         let uu____78998 = is_monadic_comp comp2  in
                         trans_G env uu____78997 uu____78998 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____79001,uu____79002) ->
             trans_F_ env e wp
         | uu____79043 -> failwith "impossible trans_F_")

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
            let uu____79051 =
              let uu____79052 = star_type' env h  in
              let uu____79055 =
                let uu____79066 =
                  let uu____79075 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____79075)  in
                [uu____79066]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____79052;
                FStar_Syntax_Syntax.effect_args = uu____79055;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____79051
          else
            (let uu____79101 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____79101)

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
    fun t  -> let uu____79122 = n env.tcenv t  in star_type' env uu____79122
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____79142 = n env.tcenv t  in check_n env uu____79142
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____79159 = n env.tcenv c  in
        let uu____79160 = n env.tcenv wp  in
        trans_F_ env uu____79159 uu____79160
  