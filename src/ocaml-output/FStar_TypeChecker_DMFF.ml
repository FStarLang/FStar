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
              let uu___613_65796 = a  in
              let uu____65797 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___613_65796.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___613_65796.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____65797
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____65810 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____65810
             then
               (d "Elaborating extra WP combinators";
                (let uu____65816 = FStar_Syntax_Print.term_to_string wp_a1
                    in
                 FStar_Util.print1 "wp_a is: %s\n" uu____65816))
             else ());
            (let rec collect_binders t =
               let uu____65835 =
                 let uu____65836 =
                   let uu____65839 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe
                     uu____65839
                    in
                 uu____65836.FStar_Syntax_Syntax.n  in
               match uu____65835 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____65874) -> t1
                     | uu____65883 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____65885 = collect_binders rest  in
                   FStar_List.append bs uu____65885
               | FStar_Syntax_Syntax.Tm_type uu____65900 -> []
               | uu____65907 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____65934 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____65934
                 FStar_Syntax_Util.name_binders
                in
             (let uu____65960 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____65960
              then
                let uu____65964 =
                  let uu____65966 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____65966  in
                d uu____65964
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____66004 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____66004 with
                | (sigelt,fv) ->
                    ((let uu____66012 =
                        let uu____66015 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____66015
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____66012);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____66139  ->
                     match uu____66139 with
                     | (t,b) ->
                         let uu____66153 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____66153))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____66192 = FStar_Syntax_Syntax.as_implicit true
                        in
                     ((FStar_Pervasives_Native.fst t), uu____66192))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____66226 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____66226)
                 in
              let uu____66229 =
                let uu____66246 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____66271 =
                        let uu____66274 = FStar_Syntax_Syntax.bv_to_name t
                           in
                        f uu____66274  in
                      FStar_Syntax_Util.arrow gamma uu____66271  in
                    let uu____66275 =
                      let uu____66276 =
                        let uu____66285 = FStar_Syntax_Syntax.mk_binder a1
                           in
                        let uu____66292 =
                          let uu____66301 = FStar_Syntax_Syntax.mk_binder t
                             in
                          [uu____66301]  in
                        uu____66285 :: uu____66292  in
                      FStar_List.append binders uu____66276  in
                    FStar_Syntax_Util.abs uu____66275 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____66332 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____66333 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____66332, uu____66333)  in
                match uu____66246 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____66375 =
                        let uu____66376 =
                          let uu____66393 =
                            let uu____66404 =
                              FStar_List.map
                                (fun uu____66426  ->
                                   match uu____66426 with
                                   | (bv,uu____66438) ->
                                       let uu____66443 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____66444 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____66443, uu____66444)) binders
                               in
                            let uu____66446 =
                              let uu____66453 =
                                let uu____66458 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____66459 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____66458, uu____66459)  in
                              let uu____66461 =
                                let uu____66468 =
                                  let uu____66473 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____66473)  in
                                [uu____66468]  in
                              uu____66453 :: uu____66461  in
                            FStar_List.append uu____66404 uu____66446  in
                          (fv, uu____66393)  in
                        FStar_Syntax_Syntax.Tm_app uu____66376  in
                      mk1 uu____66375  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____66229 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____66546 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____66546
                       in
                    let ret1 =
                      let uu____66551 =
                        let uu____66552 =
                          let uu____66555 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____66555  in
                        FStar_Syntax_Util.residual_tot uu____66552  in
                      FStar_Pervasives_Native.Some uu____66551  in
                    let body =
                      let uu____66559 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____66559 ret1  in
                    let uu____66562 =
                      let uu____66563 = mk_all_implicit binders  in
                      let uu____66570 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____66563 uu____66570  in
                    FStar_Syntax_Util.abs uu____66562 body ret1  in
                  let c_pure1 =
                    let uu____66608 = mk_lid "pure"  in
                    register env1 uu____66608 c_pure  in
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
                      let uu____66618 =
                        let uu____66619 =
                          let uu____66620 =
                            let uu____66629 =
                              let uu____66636 =
                                let uu____66637 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____66637
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____66636  in
                            [uu____66629]  in
                          let uu____66650 =
                            let uu____66653 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____66653  in
                          FStar_Syntax_Util.arrow uu____66620 uu____66650  in
                        mk_gctx uu____66619  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____66618
                       in
                    let r =
                      let uu____66656 =
                        let uu____66657 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66657  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____66656
                       in
                    let ret1 =
                      let uu____66662 =
                        let uu____66663 =
                          let uu____66666 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66666  in
                        FStar_Syntax_Util.residual_tot uu____66663  in
                      FStar_Pervasives_Native.Some uu____66662  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____66676 = FStar_Syntax_Syntax.bv_to_name l
                           in
                        let uu____66679 =
                          let uu____66690 =
                            let uu____66693 =
                              let uu____66694 =
                                let uu____66695 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____66695
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____66694  in
                            [uu____66693]  in
                          FStar_List.append gamma_as_args uu____66690  in
                        FStar_Syntax_Util.mk_app uu____66676 uu____66679  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____66698 =
                      let uu____66699 = mk_all_implicit binders  in
                      let uu____66706 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____66699 uu____66706  in
                    FStar_Syntax_Util.abs uu____66698 outer_body ret1  in
                  let c_app1 =
                    let uu____66758 = mk_lid "app"  in
                    register env1 uu____66758 c_app  in
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
                      let uu____66770 =
                        let uu____66779 =
                          let uu____66786 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____66786  in
                        [uu____66779]  in
                      let uu____66799 =
                        let uu____66802 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____66802  in
                      FStar_Syntax_Util.arrow uu____66770 uu____66799  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____66806 =
                        let uu____66807 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____66807  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____66806
                       in
                    let ret1 =
                      let uu____66812 =
                        let uu____66813 =
                          let uu____66816 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____66816  in
                        FStar_Syntax_Util.residual_tot uu____66813  in
                      FStar_Pervasives_Native.Some uu____66812  in
                    let uu____66817 =
                      let uu____66818 = mk_all_implicit binders  in
                      let uu____66825 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____66818 uu____66825  in
                    let uu____66876 =
                      let uu____66879 =
                        let uu____66890 =
                          let uu____66893 =
                            let uu____66894 =
                              let uu____66905 =
                                let uu____66908 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____66908]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____66905
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____66894  in
                          let uu____66917 =
                            let uu____66920 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____66920]  in
                          uu____66893 :: uu____66917  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____66890
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____66879  in
                    FStar_Syntax_Util.abs uu____66817 uu____66876 ret1  in
                  let c_lift11 =
                    let uu____66930 = mk_lid "lift1"  in
                    register env1 uu____66930 c_lift1  in
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
                      let uu____66944 =
                        let uu____66953 =
                          let uu____66960 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____66960  in
                        let uu____66961 =
                          let uu____66970 =
                            let uu____66977 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____66977  in
                          [uu____66970]  in
                        uu____66953 :: uu____66961  in
                      let uu____66996 =
                        let uu____66999 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____66999  in
                      FStar_Syntax_Util.arrow uu____66944 uu____66996  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____67003 =
                        let uu____67004 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____67004  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____67003
                       in
                    let a2 =
                      let uu____67007 =
                        let uu____67008 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____67008  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____67007
                       in
                    let ret1 =
                      let uu____67013 =
                        let uu____67014 =
                          let uu____67017 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____67017  in
                        FStar_Syntax_Util.residual_tot uu____67014  in
                      FStar_Pervasives_Native.Some uu____67013  in
                    let uu____67018 =
                      let uu____67019 = mk_all_implicit binders  in
                      let uu____67026 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____67019 uu____67026  in
                    let uu____67091 =
                      let uu____67094 =
                        let uu____67105 =
                          let uu____67108 =
                            let uu____67109 =
                              let uu____67120 =
                                let uu____67123 =
                                  let uu____67124 =
                                    let uu____67135 =
                                      let uu____67138 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____67138]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____67135
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1
                                    uu____67124
                                   in
                                let uu____67147 =
                                  let uu____67150 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____67150]  in
                                uu____67123 :: uu____67147  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67120
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____67109  in
                          let uu____67159 =
                            let uu____67162 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____67162]  in
                          uu____67108 :: uu____67159  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67105
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67094  in
                    FStar_Syntax_Util.abs uu____67018 uu____67091 ret1  in
                  let c_lift21 =
                    let uu____67172 = mk_lid "lift2"  in
                    register env1 uu____67172 c_lift2  in
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
                      let uu____67184 =
                        let uu____67193 =
                          let uu____67200 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____67200  in
                        [uu____67193]  in
                      let uu____67213 =
                        let uu____67216 =
                          let uu____67217 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____67217  in
                        FStar_Syntax_Syntax.mk_Total uu____67216  in
                      FStar_Syntax_Util.arrow uu____67184 uu____67213  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____67223 =
                        let uu____67224 =
                          let uu____67227 =
                            let uu____67228 =
                              let uu____67237 =
                                let uu____67244 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____67244
                                 in
                              [uu____67237]  in
                            let uu____67257 =
                              let uu____67260 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____67260  in
                            FStar_Syntax_Util.arrow uu____67228 uu____67257
                             in
                          mk_ctx uu____67227  in
                        FStar_Syntax_Util.residual_tot uu____67224  in
                      FStar_Pervasives_Native.Some uu____67223  in
                    let e1 =
                      let uu____67262 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____67262
                       in
                    let body =
                      let uu____67267 =
                        let uu____67268 =
                          let uu____67277 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____67277]  in
                        FStar_List.append gamma uu____67268  in
                      let uu____67302 =
                        let uu____67305 = FStar_Syntax_Syntax.bv_to_name f
                           in
                        let uu____67308 =
                          let uu____67319 =
                            let uu____67320 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____67320  in
                          let uu____67321 = args_of_binders1 gamma  in
                          uu____67319 :: uu____67321  in
                        FStar_Syntax_Util.mk_app uu____67305 uu____67308  in
                      FStar_Syntax_Util.abs uu____67267 uu____67302 ret1  in
                    let uu____67324 =
                      let uu____67325 = mk_all_implicit binders  in
                      let uu____67332 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____67325 uu____67332  in
                    FStar_Syntax_Util.abs uu____67324 body ret1  in
                  let c_push1 =
                    let uu____67377 = mk_lid "push"  in
                    register env1 uu____67377 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____67404 =
                        let uu____67405 =
                          let uu____67422 = args_of_binders1 binders  in
                          (c, uu____67422)  in
                        FStar_Syntax_Syntax.Tm_app uu____67405  in
                      mk1 uu____67404
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____67451 =
                        let uu____67452 =
                          let uu____67461 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____67468 =
                            let uu____67477 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____67477]  in
                          uu____67461 :: uu____67468  in
                        let uu____67502 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____67452 uu____67502  in
                      FStar_Syntax_Syntax.mk_Total uu____67451  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____67507 =
                      let uu____67508 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____67508  in
                    let uu____67523 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____67528 =
                        let uu____67531 =
                          let uu____67542 =
                            let uu____67545 =
                              let uu____67546 =
                                let uu____67557 =
                                  let uu____67566 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____67566  in
                                [uu____67557]  in
                              FStar_Syntax_Util.mk_app l_ite uu____67546  in
                            [uu____67545]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____67542
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____67531  in
                      FStar_Syntax_Util.ascribe uu____67528
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____67507 uu____67523
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____67610 = mk_lid "wp_if_then_else"  in
                    register env1 uu____67610 wp_if_then_else  in
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
                      let uu____67627 =
                        let uu____67638 =
                          let uu____67641 =
                            let uu____67642 =
                              let uu____67653 =
                                let uu____67656 =
                                  let uu____67657 =
                                    let uu____67668 =
                                      let uu____67677 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67677
                                       in
                                    [uu____67668]  in
                                  FStar_Syntax_Util.mk_app l_and uu____67657
                                   in
                                [uu____67656]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67653
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67642  in
                          let uu____67702 =
                            let uu____67705 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67705]  in
                          uu____67641 :: uu____67702  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67638
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67627  in
                    let uu____67714 =
                      let uu____67715 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67715  in
                    FStar_Syntax_Util.abs uu____67714 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____67731 = mk_lid "wp_assert"  in
                    register env1 uu____67731 wp_assert  in
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
                      let uu____67748 =
                        let uu____67759 =
                          let uu____67762 =
                            let uu____67763 =
                              let uu____67774 =
                                let uu____67777 =
                                  let uu____67778 =
                                    let uu____67789 =
                                      let uu____67798 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____67798
                                       in
                                    [uu____67789]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____67778
                                   in
                                [uu____67777]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____67774
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67763  in
                          let uu____67823 =
                            let uu____67826 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____67826]  in
                          uu____67762 :: uu____67823  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67759
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67748  in
                    let uu____67835 =
                      let uu____67836 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____67836  in
                    FStar_Syntax_Util.abs uu____67835 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____67852 = mk_lid "wp_assume"  in
                    register env1 uu____67852 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____67865 =
                        let uu____67874 =
                          let uu____67881 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____67881  in
                        [uu____67874]  in
                      let uu____67894 = FStar_Syntax_Syntax.mk_Total wp_a1
                         in
                      FStar_Syntax_Util.arrow uu____67865 uu____67894  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____67902 =
                        let uu____67913 =
                          let uu____67916 =
                            let uu____67917 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____67917  in
                          let uu____67936 =
                            let uu____67939 =
                              let uu____67940 =
                                let uu____67951 =
                                  let uu____67954 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____67954]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____67951
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____67940
                               in
                            [uu____67939]  in
                          uu____67916 :: uu____67936  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____67913
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____67902  in
                    let uu____67971 =
                      let uu____67972 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____67972  in
                    FStar_Syntax_Util.abs uu____67971 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____67988 = mk_lid "wp_close"  in
                    register env1 uu____67988 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____67999 =
                      let uu____68000 =
                        let uu____68001 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____68001
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____68000
                       in
                    FStar_Pervasives_Native.Some uu____67999  in
                  let mk_forall1 x body =
                    let uu____68013 =
                      let uu____68020 =
                        let uu____68021 =
                          let uu____68038 =
                            let uu____68049 =
                              let uu____68058 =
                                let uu____68059 =
                                  let uu____68060 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____68060]  in
                                FStar_Syntax_Util.abs uu____68059 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____68058  in
                            [uu____68049]  in
                          (FStar_Syntax_Util.tforall, uu____68038)  in
                        FStar_Syntax_Syntax.Tm_app uu____68021  in
                      FStar_Syntax_Syntax.mk uu____68020  in
                    uu____68013 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____68121 =
                      let uu____68122 = FStar_Syntax_Subst.compress t  in
                      uu____68122.FStar_Syntax_Syntax.n  in
                    match uu____68121 with
                    | FStar_Syntax_Syntax.Tm_type uu____68126 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68159  ->
                              match uu____68159 with
                              | (b,uu____68168) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____68173 -> true  in
                  let rec is_monotonic t =
                    let uu____68186 =
                      let uu____68187 = FStar_Syntax_Subst.compress t  in
                      uu____68187.FStar_Syntax_Syntax.n  in
                    match uu____68186 with
                    | FStar_Syntax_Syntax.Tm_type uu____68191 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____68224  ->
                              match uu____68224 with
                              | (b,uu____68233) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____68238 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env1 t
                       in
                    let uu____68312 =
                      let uu____68313 = FStar_Syntax_Subst.compress t1  in
                      uu____68313.FStar_Syntax_Syntax.n  in
                    match uu____68312 with
                    | FStar_Syntax_Syntax.Tm_type uu____68318 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____68321);
                                      FStar_Syntax_Syntax.pos = uu____68322;
                                      FStar_Syntax_Syntax.vars = uu____68323;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68367 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68367
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68377 =
                              let uu____68380 =
                                let uu____68391 =
                                  let uu____68400 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68400  in
                                [uu____68391]  in
                              FStar_Syntax_Util.mk_app x uu____68380  in
                            let uu____68417 =
                              let uu____68420 =
                                let uu____68431 =
                                  let uu____68440 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68440  in
                                [uu____68431]  in
                              FStar_Syntax_Util.mk_app y uu____68420  in
                            mk_rel1 b uu____68377 uu____68417  in
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
                             let uu____68464 =
                               let uu____68467 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68470 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68467 uu____68470  in
                             let uu____68473 =
                               let uu____68476 =
                                 let uu____68479 =
                                   let uu____68490 =
                                     let uu____68499 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68499
                                      in
                                   [uu____68490]  in
                                 FStar_Syntax_Util.mk_app x uu____68479  in
                               let uu____68516 =
                                 let uu____68519 =
                                   let uu____68530 =
                                     let uu____68539 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68539
                                      in
                                   [uu____68530]  in
                                 FStar_Syntax_Util.mk_app y uu____68519  in
                               mk_rel1 b uu____68476 uu____68516  in
                             FStar_Syntax_Util.mk_imp uu____68464 uu____68473
                              in
                           let uu____68556 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68556)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____68559);
                                      FStar_Syntax_Syntax.pos = uu____68560;
                                      FStar_Syntax_Syntax.vars = uu____68561;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____68605 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____68605
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____68615 =
                              let uu____68618 =
                                let uu____68629 =
                                  let uu____68638 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68638  in
                                [uu____68629]  in
                              FStar_Syntax_Util.mk_app x uu____68618  in
                            let uu____68655 =
                              let uu____68658 =
                                let uu____68669 =
                                  let uu____68678 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____68678  in
                                [uu____68669]  in
                              FStar_Syntax_Util.mk_app y uu____68658  in
                            mk_rel1 b uu____68615 uu____68655  in
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
                             let uu____68702 =
                               let uu____68705 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____68708 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____68705 uu____68708  in
                             let uu____68711 =
                               let uu____68714 =
                                 let uu____68717 =
                                   let uu____68728 =
                                     let uu____68737 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____68737
                                      in
                                   [uu____68728]  in
                                 FStar_Syntax_Util.mk_app x uu____68717  in
                               let uu____68754 =
                                 let uu____68757 =
                                   let uu____68768 =
                                     let uu____68777 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____68777
                                      in
                                   [uu____68768]  in
                                 FStar_Syntax_Util.mk_app y uu____68757  in
                               mk_rel1 b uu____68714 uu____68754  in
                             FStar_Syntax_Util.mk_imp uu____68702 uu____68711
                              in
                           let uu____68794 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____68794)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___827_68833 = t1  in
                          let uu____68834 =
                            let uu____68835 =
                              let uu____68850 =
                                let uu____68853 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____68853  in
                              ([binder], uu____68850)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____68835  in
                          {
                            FStar_Syntax_Syntax.n = uu____68834;
                            FStar_Syntax_Syntax.pos =
                              (uu___827_68833.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___827_68833.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____68876 ->
                        failwith "unhandled arrow"
                    | uu____68894 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____68931 =
                        let uu____68932 = FStar_Syntax_Subst.compress t1  in
                        uu____68932.FStar_Syntax_Syntax.n  in
                      match uu____68931 with
                      | FStar_Syntax_Syntax.Tm_type uu____68935 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____68962 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____68962
                          ->
                          let project i tuple =
                            let projector =
                              let uu____68983 =
                                let uu____68984 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____68984 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____68983
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____69014 =
                            let uu____69025 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____69043  ->
                                     match uu____69043 with
                                     | (t2,q) ->
                                         let uu____69063 = project i x  in
                                         let uu____69066 = project i y  in
                                         mk_stronger t2 uu____69063
                                           uu____69066) args
                               in
                            match uu____69025 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____69014 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____69120);
                                      FStar_Syntax_Syntax.pos = uu____69121;
                                      FStar_Syntax_Syntax.vars = uu____69122;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69166  ->
                                   match uu____69166 with
                                   | (bv,q) ->
                                       let uu____69180 =
                                         let uu____69182 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69182  in
                                       FStar_Syntax_Syntax.gen_bv uu____69180
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69191 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69191) bvs
                             in
                          let body =
                            let uu____69193 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69196 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69193 uu____69196  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____69205);
                                      FStar_Syntax_Syntax.pos = uu____69206;
                                      FStar_Syntax_Syntax.vars = uu____69207;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____69251  ->
                                   match uu____69251 with
                                   | (bv,q) ->
                                       let uu____69265 =
                                         let uu____69267 =
                                           FStar_Util.string_of_int i  in
                                         Prims.op_Hat "a" uu____69267  in
                                       FStar_Syntax_Syntax.gen_bv uu____69265
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____69276 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____69276) bvs
                             in
                          let body =
                            let uu____69278 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____69281 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____69278 uu____69281  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____69288 -> failwith "Not a DM elaborated type"
                       in
                    let body =
                      let uu____69291 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____69294 = FStar_Syntax_Syntax.bv_to_name wp1
                         in
                      let uu____69297 = FStar_Syntax_Syntax.bv_to_name wp2
                         in
                      mk_stronger uu____69291 uu____69294 uu____69297  in
                    let uu____69300 =
                      let uu____69301 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____69301  in
                    FStar_Syntax_Util.abs uu____69300 body ret_tot_type  in
                  let stronger1 =
                    let uu____69343 = mk_lid "stronger"  in
                    register env1 uu____69343 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69351 = FStar_Util.prefix gamma  in
                    match uu____69351 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____69417 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____69417
                             in
                          let uu____69422 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____69422 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____69432 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____69432  in
                              let guard_free1 =
                                let uu____69444 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____69444  in
                              let pat =
                                let uu____69448 =
                                  let uu____69459 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____69459]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____69448
                                 in
                              let pattern_guarded_body =
                                let uu____69487 =
                                  let uu____69488 =
                                    let uu____69495 =
                                      let uu____69496 =
                                        let uu____69509 =
                                          let uu____69520 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____69520]  in
                                        [uu____69509]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____69496
                                       in
                                    (body, uu____69495)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____69488  in
                                mk1 uu____69487  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____69567 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____69576 =
                            let uu____69579 =
                              let uu____69580 =
                                let uu____69583 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____69586 =
                                  let uu____69597 = args_of_binders1 wp_args
                                     in
                                  let uu____69600 =
                                    let uu____69603 =
                                      let uu____69604 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____69604
                                       in
                                    [uu____69603]  in
                                  FStar_List.append uu____69597 uu____69600
                                   in
                                FStar_Syntax_Util.mk_app uu____69583
                                  uu____69586
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____69580  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____69579
                             in
                          FStar_Syntax_Util.abs gamma uu____69576
                            ret_gtot_type
                           in
                        let uu____69605 =
                          let uu____69606 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____69606  in
                        FStar_Syntax_Util.abs uu____69605 body ret_gtot_type
                     in
                  let ite_wp1 =
                    let uu____69622 = mk_lid "ite_wp"  in
                    register env1 uu____69622 ite_wp  in
                  let ite_wp2 = mk_generic_app ite_wp1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____69630 = FStar_Util.prefix gamma  in
                    match uu____69630 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____69688 =
                            let uu____69689 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____69696 =
                              let uu____69707 =
                                let uu____69716 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____69716  in
                              [uu____69707]  in
                            FStar_Syntax_Util.mk_app uu____69689 uu____69696
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____69688
                           in
                        let uu____69733 =
                          let uu____69734 =
                            let uu____69743 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____69743 gamma  in
                          FStar_List.append binders uu____69734  in
                        FStar_Syntax_Util.abs uu____69733 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____69765 = mk_lid "null_wp"  in
                    register env1 uu____69765 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____69778 =
                        let uu____69789 =
                          let uu____69792 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____69793 =
                            let uu____69796 =
                              let uu____69797 =
                                let uu____69808 =
                                  let uu____69817 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____69817  in
                                [uu____69808]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____69797
                               in
                            let uu____69834 =
                              let uu____69837 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____69837]  in
                            uu____69796 :: uu____69834  in
                          uu____69792 :: uu____69793  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____69789
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____69778  in
                    let uu____69846 =
                      let uu____69847 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____69847  in
                    FStar_Syntax_Util.abs uu____69846 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____69863 = mk_lid "wp_trivial"  in
                    register env1 uu____69863 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____69869 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____69869
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____69881 =
                      let uu____69882 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____69882  in
                    let uu____69930 =
                      let uu___934_69931 = ed  in
                      let uu____69932 =
                        let uu____69933 = c wp_if_then_else2  in
                        ([], uu____69933)  in
                      let uu____69940 =
                        let uu____69941 = c ite_wp2  in ([], uu____69941)  in
                      let uu____69948 =
                        let uu____69949 = c stronger2  in ([], uu____69949)
                         in
                      let uu____69956 =
                        let uu____69957 = c wp_close2  in ([], uu____69957)
                         in
                      let uu____69964 =
                        let uu____69965 = c wp_assert2  in ([], uu____69965)
                         in
                      let uu____69972 =
                        let uu____69973 = c wp_assume2  in ([], uu____69973)
                         in
                      let uu____69980 =
                        let uu____69981 = c null_wp2  in ([], uu____69981)
                         in
                      let uu____69988 =
                        let uu____69989 = c wp_trivial2  in ([], uu____69989)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___934_69931.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___934_69931.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___934_69931.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___934_69931.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___934_69931.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___934_69931.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___934_69931.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____69932;
                        FStar_Syntax_Syntax.ite_wp = uu____69940;
                        FStar_Syntax_Syntax.stronger = uu____69948;
                        FStar_Syntax_Syntax.close_wp = uu____69956;
                        FStar_Syntax_Syntax.assert_p = uu____69964;
                        FStar_Syntax_Syntax.assume_p = uu____69972;
                        FStar_Syntax_Syntax.null_wp = uu____69980;
                        FStar_Syntax_Syntax.trivial = uu____69988;
                        FStar_Syntax_Syntax.repr =
                          (uu___934_69931.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___934_69931.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___934_69931.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___934_69931.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___934_69931.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____69881, uu____69930)))))
  
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.tcenv 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___939_70013 = dmff_env  in
      {
        tcenv = env';
        subst = (uu___939_70013.subst);
        tc_const = (uu___939_70013.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | N _0 -> true | uu____70034 -> false
  
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  ->
    match projectee with | M _0 -> true | uu____70054 -> false
  
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____70075) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___585_70089  ->
                match uu___585_70089 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____70092 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu____70094 ->
        let uu____70095 =
          let uu____70101 =
            let uu____70103 = FStar_Syntax_Print.comp_to_string c  in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu____70103
             in
          (FStar_Errors.Error_UnexpectedDM4FType, uu____70101)  in
        FStar_Errors.raise_error uu____70095 c.FStar_Syntax_Syntax.pos
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___586_70113  ->
    match uu___586_70113 with
    | N t ->
        let uu____70116 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____70116
    | M t ->
        let uu____70120 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____70120
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____70129,c) -> nm_of_comp c
    | uu____70151 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____70164 = nm_of_comp c  in
    match uu____70164 with | M uu____70166 -> true | N uu____70168 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____70179 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____70195 =
        let uu____70204 =
          let uu____70211 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____70211  in
        [uu____70204]  in
      let uu____70230 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____70195 uu____70230  in
    let uu____70233 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____70233
  
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
        let uu____70275 =
          let uu____70276 =
            let uu____70291 =
              let uu____70300 =
                let uu____70307 =
                  let uu____70308 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____70308  in
                let uu____70309 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____70307, uu____70309)  in
              [uu____70300]  in
            let uu____70327 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____70291, uu____70327)  in
          FStar_Syntax_Syntax.Tm_arrow uu____70276  in
        mk1 uu____70275

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____70367) ->
          let binders1 =
            FStar_List.map
              (fun uu____70413  ->
                 match uu____70413 with
                 | (bv,aqual) ->
                     let uu____70432 =
                       let uu___989_70433 = bv  in
                       let uu____70434 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___989_70433.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___989_70433.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____70434
                       }  in
                     (uu____70432, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____70439,{
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.GTotal (hn,uu____70441);
                              FStar_Syntax_Syntax.pos = uu____70442;
                              FStar_Syntax_Syntax.vars = uu____70443;_})
               ->
               let uu____70472 =
                 let uu____70473 =
                   let uu____70488 =
                     let uu____70491 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____70491  in
                   (binders1, uu____70488)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____70473  in
               mk1 uu____70472
           | uu____70502 ->
               let uu____70503 = is_monadic_arrow t1.FStar_Syntax_Syntax.n
                  in
               (match uu____70503 with
                | N hn ->
                    let uu____70505 =
                      let uu____70506 =
                        let uu____70521 =
                          let uu____70524 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____70524  in
                        (binders1, uu____70521)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70506  in
                    mk1 uu____70505
                | M a ->
                    let uu____70536 =
                      let uu____70537 =
                        let uu____70552 =
                          let uu____70561 =
                            let uu____70570 =
                              let uu____70577 =
                                let uu____70578 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____70578  in
                              let uu____70579 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____70577, uu____70579)  in
                            [uu____70570]  in
                          FStar_List.append binders1 uu____70561  in
                        let uu____70603 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____70552, uu____70603)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____70537  in
                    mk1 uu____70536))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____70697 = f x  in
                    FStar_Util.string_builder_append strb uu____70697);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____70706 = f x1  in
                         FStar_Util.string_builder_append strb uu____70706))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____70710 =
              let uu____70716 =
                let uu____70718 = FStar_Syntax_Print.term_to_string t2  in
                let uu____70720 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____70718 uu____70720
                 in
              (FStar_Errors.Warning_DependencyFound, uu____70716)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____70710  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____70742 =
              let uu____70743 = FStar_Syntax_Subst.compress ty  in
              uu____70743.FStar_Syntax_Syntax.n  in
            match uu____70742 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____70769 =
                  let uu____70771 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____70771  in
                if uu____70769
                then false
                else
                  (try
                     (fun uu___1038_70788  ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu____70812 = FStar_Syntax_Free.names ty1
                                   in
                                FStar_Util.set_intersect uu____70812 s  in
                              let uu____70815 =
                                let uu____70817 =
                                  FStar_Util.set_is_empty sinter  in
                                Prims.op_Negation uu____70817  in
                              if uu____70815
                              then
                                (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                              else ()  in
                            let uu____70823 =
                              FStar_Syntax_Subst.open_comp binders c  in
                            (match uu____70823 with
                             | (binders1,c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s  ->
                                        fun uu____70848  ->
                                          match uu____70848 with
                                          | (bv,uu____70860) ->
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
            | uu____70888 ->
                ((let uu____70890 =
                    let uu____70896 =
                      let uu____70898 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____70898
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____70896)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____70890);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____70914 =
              let uu____70915 = FStar_Syntax_Subst.compress head2  in
              uu____70915.FStar_Syntax_Syntax.n  in
            match uu____70914 with
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
                  (let uu____70921 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____70921)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____70924 =
                  FStar_TypeChecker_Env.lookup_lid env.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____70924 with
                 | ((uu____70934,ty),uu____70936) ->
                     let uu____70941 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____70941
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env.tcenv t1
                          in
                       let uu____70954 =
                         let uu____70955 = FStar_Syntax_Subst.compress res
                            in
                         uu____70955.FStar_Syntax_Syntax.n  in
                       (match uu____70954 with
                        | FStar_Syntax_Syntax.Tm_app uu____70959 -> true
                        | uu____70977 ->
                            ((let uu____70979 =
                                let uu____70985 =
                                  let uu____70987 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____70987
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____70985)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____70979);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____70995 -> true
            | FStar_Syntax_Syntax.Tm_name uu____70997 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____71000) ->
                is_valid_application t2
            | uu____71005 -> false  in
          let uu____71007 = is_valid_application head1  in
          if uu____71007
          then
            let uu____71010 =
              let uu____71011 =
                let uu____71028 =
                  FStar_List.map
                    (fun uu____71057  ->
                       match uu____71057 with
                       | (t2,qual) ->
                           let uu____71082 = star_type' env t2  in
                           (uu____71082, qual)) args
                   in
                (head1, uu____71028)  in
              FStar_Syntax_Syntax.Tm_app uu____71011  in
            mk1 uu____71010
          else
            (let uu____71099 =
               let uu____71105 =
                 let uu____71107 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____71107
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____71105)  in
             FStar_Errors.raise_err uu____71099)
      | FStar_Syntax_Syntax.Tm_bvar uu____71111 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____71112 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____71113 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____71114 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____71142 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____71142 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___1110_71150 = env  in
                 let uu____71151 =
                   FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
                 {
                   tcenv = uu____71151;
                   subst = (uu___1110_71150.subst);
                   tc_const = (uu___1110_71150.tc_const)
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
               ((let uu___1125_71178 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___1125_71178.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___1125_71178.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____71185 =
            let uu____71186 =
              let uu____71193 = star_type' env t2  in (uu____71193, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____71186  in
          mk1 uu____71185
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____71245 =
            let uu____71246 =
              let uu____71273 = star_type' env e  in
              let uu____71276 =
                let uu____71293 =
                  let uu____71302 = star_type' env t2  in
                  FStar_Util.Inl uu____71302  in
                (uu____71293, FStar_Pervasives_Native.None)  in
              (uu____71273, uu____71276, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71246  in
          mk1 uu____71245
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____71390 =
            let uu____71391 =
              let uu____71418 = star_type' env e  in
              let uu____71421 =
                let uu____71438 =
                  let uu____71447 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____71447  in
                (uu____71438, FStar_Pervasives_Native.None)  in
              (uu____71418, uu____71421, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____71391  in
          mk1 uu____71390
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____71488,(uu____71489,FStar_Pervasives_Native.Some uu____71490),uu____71491)
          ->
          let uu____71540 =
            let uu____71546 =
              let uu____71548 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____71548
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71546)  in
          FStar_Errors.raise_err uu____71540
      | FStar_Syntax_Syntax.Tm_refine uu____71552 ->
          let uu____71559 =
            let uu____71565 =
              let uu____71567 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____71567
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71565)  in
          FStar_Errors.raise_err uu____71559
      | FStar_Syntax_Syntax.Tm_uinst uu____71571 ->
          let uu____71578 =
            let uu____71584 =
              let uu____71586 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____71586
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71584)  in
          FStar_Errors.raise_err uu____71578
      | FStar_Syntax_Syntax.Tm_quoted uu____71590 ->
          let uu____71597 =
            let uu____71603 =
              let uu____71605 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____71605
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71603)  in
          FStar_Errors.raise_err uu____71597
      | FStar_Syntax_Syntax.Tm_constant uu____71609 ->
          let uu____71610 =
            let uu____71616 =
              let uu____71618 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____71618
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71616)  in
          FStar_Errors.raise_err uu____71610
      | FStar_Syntax_Syntax.Tm_match uu____71622 ->
          let uu____71645 =
            let uu____71651 =
              let uu____71653 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____71653
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71651)  in
          FStar_Errors.raise_err uu____71645
      | FStar_Syntax_Syntax.Tm_let uu____71657 ->
          let uu____71671 =
            let uu____71677 =
              let uu____71679 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s"
                uu____71679
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71677)  in
          FStar_Errors.raise_err uu____71671
      | FStar_Syntax_Syntax.Tm_uvar uu____71683 ->
          let uu____71696 =
            let uu____71702 =
              let uu____71704 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____71704
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71702)  in
          FStar_Errors.raise_err uu____71696
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____71708 =
            let uu____71714 =
              let uu____71716 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____71716
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____71714)  in
          FStar_Errors.raise_err uu____71708
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____71721 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____71721
      | FStar_Syntax_Syntax.Tm_delayed uu____71724 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___588_71756  ->
    match uu___588_71756 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___587_71767  ->
                match uu___587_71767 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____71770 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____71780 =
      let uu____71781 = FStar_Syntax_Subst.compress t  in
      uu____71781.FStar_Syntax_Syntax.n  in
    match uu____71780 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____71813 =
            let uu____71814 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____71814  in
          is_C uu____71813  in
        if r
        then
          ((let uu____71838 =
              let uu____71840 =
                FStar_List.for_all
                  (fun uu____71851  ->
                     match uu____71851 with | (h,uu____71860) -> is_C h) args
                 in
              Prims.op_Negation uu____71840  in
            if uu____71838 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____71873 =
              let uu____71875 =
                FStar_List.for_all
                  (fun uu____71887  ->
                     match uu____71887 with
                     | (h,uu____71896) ->
                         let uu____71901 = is_C h  in
                         Prims.op_Negation uu____71901) args
                 in
              Prims.op_Negation uu____71875  in
            if uu____71873 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____71930 = nm_of_comp comp  in
        (match uu____71930 with
         | M t1 ->
             ((let uu____71934 = is_C t1  in
               if uu____71934 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____71943) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____71949) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____71955,uu____71956) -> is_C t1
    | uu____71997 -> false
  
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
          let uu____72033 =
            let uu____72034 =
              let uu____72051 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____72054 =
                let uu____72065 =
                  let uu____72074 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____72074)  in
                [uu____72065]  in
              (uu____72051, uu____72054)  in
            FStar_Syntax_Syntax.Tm_app uu____72034  in
          mk1 uu____72033  in
        let uu____72110 =
          let uu____72111 = FStar_Syntax_Syntax.mk_binder p  in [uu____72111]
           in
        FStar_Syntax_Util.abs uu____72110 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___589_72136  ->
    match uu___589_72136 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____72139 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____72377 =
          match uu____72377 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____72414 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____72417 =
                       let uu____72419 =
                         FStar_TypeChecker_Rel.teq env.tcenv t1 t2  in
                       FStar_TypeChecker_Env.is_trivial uu____72419  in
                     Prims.op_Negation uu____72417)
                   in
                if uu____72414
                then
                  let uu____72421 =
                    let uu____72427 =
                      let uu____72429 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____72431 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____72433 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____72429 uu____72431 uu____72433
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____72427)  in
                  FStar_Errors.raise_err uu____72421
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____72458 = mk_return env t1 s_e  in
                     ((M t1), uu____72458, u_e)))
               | (M t1,N t2) ->
                   let uu____72465 =
                     let uu____72471 =
                       let uu____72473 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____72475 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____72477 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____72473 uu____72475 uu____72477
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____72471)
                      in
                   FStar_Errors.raise_err uu____72465)
           in
        let ensure_m env1 e2 =
          let strip_m uu___590_72529 =
            match uu___590_72529 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____72545 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____72566 =
                let uu____72572 =
                  let uu____72574 = FStar_Syntax_Print.term_to_string t  in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____72574
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____72572)  in
              FStar_Errors.raise_error uu____72566 e2.FStar_Syntax_Syntax.pos
          | M uu____72584 ->
              let uu____72585 = check env1 e2 context_nm  in
              strip_m uu____72585
           in
        let uu____72592 =
          let uu____72593 = FStar_Syntax_Subst.compress e  in
          uu____72593.FStar_Syntax_Syntax.n  in
        match uu____72592 with
        | FStar_Syntax_Syntax.Tm_bvar uu____72602 ->
            let uu____72603 = infer env e  in return_if uu____72603
        | FStar_Syntax_Syntax.Tm_name uu____72610 ->
            let uu____72611 = infer env e  in return_if uu____72611
        | FStar_Syntax_Syntax.Tm_fvar uu____72618 ->
            let uu____72619 = infer env e  in return_if uu____72619
        | FStar_Syntax_Syntax.Tm_abs uu____72626 ->
            let uu____72645 = infer env e  in return_if uu____72645
        | FStar_Syntax_Syntax.Tm_constant uu____72652 ->
            let uu____72653 = infer env e  in return_if uu____72653
        | FStar_Syntax_Syntax.Tm_quoted uu____72660 ->
            let uu____72667 = infer env e  in return_if uu____72667
        | FStar_Syntax_Syntax.Tm_app uu____72674 ->
            let uu____72691 = infer env e  in return_if uu____72691
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____72699 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____72699 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____72764) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____72770) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____72776,uu____72777) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____72818 ->
            let uu____72832 =
              let uu____72834 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____72834  in
            failwith uu____72832
        | FStar_Syntax_Syntax.Tm_type uu____72843 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____72851 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____72873 ->
            let uu____72880 =
              let uu____72882 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____72882  in
            failwith uu____72880
        | FStar_Syntax_Syntax.Tm_uvar uu____72891 ->
            let uu____72904 =
              let uu____72906 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____72906  in
            failwith uu____72904
        | FStar_Syntax_Syntax.Tm_delayed uu____72915 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____72945 =
              let uu____72947 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____72947  in
            failwith uu____72945

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
      let uu____72977 =
        let uu____72978 = FStar_Syntax_Subst.compress e  in
        uu____72978.FStar_Syntax_Syntax.n  in
      match uu____72977 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____72997 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____72997
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____73048;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____73049;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____73055 =
                  let uu___1360_73056 = rc  in
                  let uu____73057 =
                    let uu____73062 =
                      let uu____73065 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____73065  in
                    FStar_Pervasives_Native.Some uu____73062  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___1360_73056.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____73057;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___1360_73056.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____73055
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___1366_73077 = env  in
            let uu____73078 =
              FStar_TypeChecker_Env.push_binders env.tcenv binders1  in
            {
              tcenv = uu____73078;
              subst = (uu___1366_73077.subst);
              tc_const = (uu___1366_73077.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____73104  ->
                 match uu____73104 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___1373_73127 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___1373_73127.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___1373_73127.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____73128 =
            FStar_List.fold_left
              (fun uu____73159  ->
                 fun uu____73160  ->
                   match (uu____73159, uu____73160) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____73218 = is_C c  in
                       if uu____73218
                       then
                         let xw =
                           let uu____73228 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.op_Hat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____73228
                            in
                         let x =
                           let uu___1385_73231 = bv  in
                           let uu____73232 =
                             let uu____73235 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____73235  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___1385_73231.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___1385_73231.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____73232
                           }  in
                         let env3 =
                           let uu___1388_73237 = env2  in
                           let uu____73238 =
                             let uu____73241 =
                               let uu____73242 =
                                 let uu____73249 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____73249)  in
                               FStar_Syntax_Syntax.NT uu____73242  in
                             uu____73241 :: (env2.subst)  in
                           {
                             tcenv = (uu___1388_73237.tcenv);
                             subst = uu____73238;
                             tc_const = (uu___1388_73237.tc_const)
                           }  in
                         let uu____73254 =
                           let uu____73257 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____73258 =
                             let uu____73261 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____73261 :: acc  in
                           uu____73257 :: uu____73258  in
                         (env3, uu____73254)
                       else
                         (let x =
                            let uu___1391_73267 = bv  in
                            let uu____73268 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1391_73267.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1391_73267.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____73268
                            }  in
                          let uu____73271 =
                            let uu____73274 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____73274 :: acc  in
                          (env2, uu____73271))) (env1, []) binders1
             in
          (match uu____73128 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____73294 =
                 let check_what =
                   let uu____73320 = is_monadic rc_opt1  in
                   if uu____73320 then check_m else check_n  in
                 let uu____73337 = check_what env2 body1  in
                 match uu____73337 with
                 | (t,s_body,u_body) ->
                     let uu____73357 =
                       let uu____73360 =
                         let uu____73361 = is_monadic rc_opt1  in
                         if uu____73361 then M t else N t  in
                       comp_of_nm uu____73360  in
                     (uu____73357, s_body, u_body)
                  in
               (match uu____73294 with
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
                                 let uu____73401 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___591_73407  ->
                                           match uu___591_73407 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____73410 -> false))
                                    in
                                 if uu____73401
                                 then
                                   let uu____73413 =
                                     FStar_List.filter
                                       (fun uu___592_73417  ->
                                          match uu___592_73417 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____73420 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____73413
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____73431 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___593_73437  ->
                                         match uu___593_73437 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____73440 -> false))
                                  in
                               if uu____73431
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___594_73449  ->
                                        match uu___594_73449 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____73452 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____73454 =
                                   let uu____73455 =
                                     let uu____73460 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____73460
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____73455 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____73454
                               else
                                 (let uu____73467 =
                                    let uu___1432_73468 = rc  in
                                    let uu____73469 =
                                      let uu____73474 = star_type' env2 rt
                                         in
                                      FStar_Pervasives_Native.Some
                                        uu____73474
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_73468.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____73469;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_73468.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____73467))
                       in
                    let uu____73479 =
                      let comp1 =
                        let uu____73487 = is_monadic rc_opt1  in
                        let uu____73489 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____73487 uu____73489
                         in
                      let uu____73490 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____73490,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____73479 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____73528 =
                             let uu____73529 =
                               let uu____73548 =
                                 let uu____73551 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____73551 s_rc_opt  in
                               (s_binders1, s_body1, uu____73548)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73529  in
                           mk1 uu____73528  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____73571 =
                             let uu____73572 =
                               let uu____73591 =
                                 let uu____73594 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____73594 u_rc_opt  in
                               (u_binders2, u_body2, uu____73591)  in
                             FStar_Syntax_Syntax.Tm_abs uu____73572  in
                           mk1 uu____73571  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____73610;_};
            FStar_Syntax_Syntax.fv_delta = uu____73611;
            FStar_Syntax_Syntax.fv_qual = uu____73612;_}
          ->
          let uu____73615 =
            let uu____73620 = FStar_TypeChecker_Env.lookup_lid env.tcenv lid
               in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____73620  in
          (match uu____73615 with
           | (uu____73651,t) ->
               let uu____73653 =
                 let uu____73654 = normalize1 t  in N uu____73654  in
               (uu____73653, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____73655;
             FStar_Syntax_Syntax.vars = uu____73656;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73735 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73735 with
           | (unary_op1,uu____73759) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____73830;
             FStar_Syntax_Syntax.vars = uu____73831;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____73927 = FStar_Syntax_Util.head_and_args e  in
          (match uu____73927 with
           | (unary_op1,uu____73951) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74030;
             FStar_Syntax_Syntax.vars = uu____74031;_},(a,FStar_Pervasives_Native.None
                                                        )::[])
          ->
          let uu____74069 = infer env a  in
          (match uu____74069 with
           | (t,s,u) ->
               let uu____74085 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74085 with
                | (head1,uu____74109) ->
                    let uu____74134 =
                      let uu____74135 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____74135  in
                    let uu____74136 =
                      let uu____74137 =
                        let uu____74138 =
                          let uu____74155 =
                            let uu____74166 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74166]  in
                          (head1, uu____74155)  in
                        FStar_Syntax_Syntax.Tm_app uu____74138  in
                      mk1 uu____74137  in
                    let uu____74203 =
                      let uu____74204 =
                        let uu____74205 =
                          let uu____74222 =
                            let uu____74233 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74233]  in
                          (head1, uu____74222)  in
                        FStar_Syntax_Syntax.Tm_app uu____74205  in
                      mk1 uu____74204  in
                    (uu____74134, uu____74136, uu____74203)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74270;
             FStar_Syntax_Syntax.vars = uu____74271;_},(a1,uu____74273)::a2::[])
          ->
          let uu____74329 = infer env a1  in
          (match uu____74329 with
           | (t,s,u) ->
               let uu____74345 = FStar_Syntax_Util.head_and_args e  in
               (match uu____74345 with
                | (head1,uu____74369) ->
                    let uu____74394 =
                      let uu____74395 =
                        let uu____74396 =
                          let uu____74413 =
                            let uu____74424 = FStar_Syntax_Syntax.as_arg s
                               in
                            [uu____74424; a2]  in
                          (head1, uu____74413)  in
                        FStar_Syntax_Syntax.Tm_app uu____74396  in
                      mk1 uu____74395  in
                    let uu____74469 =
                      let uu____74470 =
                        let uu____74471 =
                          let uu____74488 =
                            let uu____74499 = FStar_Syntax_Syntax.as_arg u
                               in
                            [uu____74499; a2]  in
                          (head1, uu____74488)  in
                        FStar_Syntax_Syntax.Tm_app uu____74471  in
                      mk1 uu____74470  in
                    (t, uu____74394, uu____74469)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____74544;
             FStar_Syntax_Syntax.vars = uu____74545;_},uu____74546)
          ->
          let uu____74571 =
            let uu____74577 =
              let uu____74579 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74579
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74577)  in
          FStar_Errors.raise_error uu____74571 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____74589;
             FStar_Syntax_Syntax.vars = uu____74590;_},uu____74591)
          ->
          let uu____74616 =
            let uu____74622 =
              let uu____74624 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____74624
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____74622)  in
          FStar_Errors.raise_error uu____74616 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____74660 = check_n env head1  in
          (match uu____74660 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____74683 =
                   let uu____74684 = FStar_Syntax_Subst.compress t  in
                   uu____74684.FStar_Syntax_Syntax.n  in
                 match uu____74683 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____74688 -> true
                 | uu____74704 -> false  in
               let rec flatten1 t =
                 let uu____74726 =
                   let uu____74727 = FStar_Syntax_Subst.compress t  in
                   uu____74727.FStar_Syntax_Syntax.n  in
                 match uu____74726 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____74746);
                                FStar_Syntax_Syntax.pos = uu____74747;
                                FStar_Syntax_Syntax.vars = uu____74748;_})
                     when is_arrow t1 ->
                     let uu____74777 = flatten1 t1  in
                     (match uu____74777 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (e1,uu____74877,uu____74878) -> flatten1 e1
                 | uu____74919 ->
                     let uu____74920 =
                       let uu____74926 =
                         let uu____74928 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____74928
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____74926)  in
                     FStar_Errors.raise_err uu____74920
                  in
               let uu____74946 = flatten1 t_head  in
               (match uu____74946 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____75021 =
                          let uu____75027 =
                            let uu____75029 = FStar_Util.string_of_int n1  in
                            let uu____75037 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____75049 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____75029 uu____75037 uu____75049
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____75027)
                           in
                        FStar_Errors.raise_err uu____75021)
                     else ();
                     (let uu____75061 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____75061 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____75114 args1 =
                            match uu____75114 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____75214 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         comp2
                                        in
                                     nm_of_comp uu____75214
                                 | (binders3,[]) ->
                                     let uu____75252 =
                                       let uu____75253 =
                                         let uu____75256 =
                                           let uu____75257 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____75257
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____75256
                                          in
                                       uu____75253.FStar_Syntax_Syntax.n  in
                                     (match uu____75252 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____75290 =
                                            let uu____75291 =
                                              let uu____75292 =
                                                let uu____75307 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____75307)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____75292
                                               in
                                            mk1 uu____75291  in
                                          N uu____75290
                                      | uu____75320 -> failwith "wat?")
                                 | ([],uu____75322::uu____75323) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____75376)::binders3,(arg,uu____75379)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____75466 = FStar_List.splitAt n' binders1
                             in
                          (match uu____75466 with
                           | (binders2,uu____75504) ->
                               let uu____75537 =
                                 let uu____75560 =
                                   FStar_List.map2
                                     (fun uu____75622  ->
                                        fun uu____75623  ->
                                          match (uu____75622, uu____75623)
                                          with
                                          | ((bv,uu____75671),(arg,q)) ->
                                              let uu____75700 =
                                                let uu____75701 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____75701.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____75700 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____75722 ->
                                                   let uu____75723 =
                                                     let uu____75730 =
                                                       star_type' env arg  in
                                                     (uu____75730, q)  in
                                                   (uu____75723, [(arg, q)])
                                               | uu____75767 ->
                                                   let uu____75768 =
                                                     check_n env arg  in
                                                   (match uu____75768 with
                                                    | (uu____75793,s_arg,u_arg)
                                                        ->
                                                        let uu____75796 =
                                                          let uu____75805 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____75805
                                                          then
                                                            let uu____75816 =
                                                              let uu____75823
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____75823,
                                                                q)
                                                               in
                                                            [uu____75816;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____75796))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____75560  in
                               (match uu____75537 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____75951 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____75964 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____75951, uu____75964)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____76033) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____76039) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____76045,uu____76046) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____76088 =
            let uu____76089 = env.tc_const c  in N uu____76089  in
          (uu____76088, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____76096 ->
          let uu____76110 =
            let uu____76112 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____76112  in
          failwith uu____76110
      | FStar_Syntax_Syntax.Tm_type uu____76121 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____76129 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____76151 ->
          let uu____76158 =
            let uu____76160 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____76160  in
          failwith uu____76158
      | FStar_Syntax_Syntax.Tm_uvar uu____76169 ->
          let uu____76182 =
            let uu____76184 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____76184  in
          failwith uu____76182
      | FStar_Syntax_Syntax.Tm_delayed uu____76193 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____76223 =
            let uu____76225 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____76225  in
          failwith uu____76223

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
          let uu____76274 = check_n env e0  in
          match uu____76274 with
          | (uu____76287,s_e0,u_e0) ->
              let uu____76290 =
                let uu____76319 =
                  FStar_List.map
                    (fun b  ->
                       let uu____76380 = FStar_Syntax_Subst.open_branch b  in
                       match uu____76380 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___1707_76422 = env  in
                             let uu____76423 =
                               let uu____76424 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.tcenv
                                 uu____76424
                                in
                             {
                               tcenv = uu____76423;
                               subst = (uu___1707_76422.subst);
                               tc_const = (uu___1707_76422.tc_const)
                             }  in
                           let uu____76427 = f env1 body  in
                           (match uu____76427 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____76499 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____76319  in
              (match uu____76290 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____76605 = FStar_List.hd nms  in
                     match uu____76605 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___595_76614  ->
                          match uu___595_76614 with
                          | M uu____76616 -> true
                          | uu____76618 -> false) nms
                      in
                   let uu____76620 =
                     let uu____76657 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____76747  ->
                              match uu____76747 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____76931 =
                                         check env original_body (M t2)  in
                                       (match uu____76931 with
                                        | (uu____76968,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____77007,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____76657  in
                   (match uu____76620 with
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
                              (fun uu____77196  ->
                                 match uu____77196 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____77247 =
                                         let uu____77248 =
                                           let uu____77265 =
                                             let uu____77276 =
                                               let uu____77285 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____77288 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____77285, uu____77288)  in
                                             [uu____77276]  in
                                           (s_body, uu____77265)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____77248
                                          in
                                       mk1 uu____77247  in
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
                            let uu____77423 =
                              let uu____77424 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____77424]  in
                            let uu____77443 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____77423 uu____77443
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____77467 =
                              let uu____77476 =
                                let uu____77483 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____77483
                                 in
                              [uu____77476]  in
                            let uu____77502 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____77467 uu____77502
                             in
                          let uu____77505 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____77544 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____77505, uu____77544)
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
                           let uu____77654 =
                             let uu____77655 =
                               let uu____77656 =
                                 let uu____77683 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____77683,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____77656
                                in
                             mk1 uu____77655  in
                           let uu____77742 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____77654, uu____77742))))

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
              let uu____77807 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____77807]  in
            let uu____77826 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____77826 with
            | (x_binders1,e21) ->
                let uu____77839 = infer env e1  in
                (match uu____77839 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____77856 = is_C t1  in
                       if uu____77856
                       then
                         let uu___1793_77859 = binding  in
                         let uu____77860 =
                           let uu____77863 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____77863  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___1793_77859.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___1793_77859.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____77860;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___1793_77859.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___1793_77859.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___1793_77859.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___1793_77859.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___1796_77867 = env  in
                       let uu____77868 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1798_77870 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1798_77870.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1798_77870.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____77868;
                         subst = (uu___1796_77867.subst);
                         tc_const = (uu___1796_77867.tc_const)
                       }  in
                     let uu____77871 = proceed env1 e21  in
                     (match uu____77871 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___1805_77888 = binding  in
                            let uu____77889 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___1805_77888.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___1805_77888.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____77889;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___1805_77888.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___1805_77888.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___1805_77888.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___1805_77888.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____77892 =
                            let uu____77893 =
                              let uu____77894 =
                                let uu____77908 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___1808_77925 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1808_77925.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1808_77925.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1808_77925.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1808_77925.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1808_77925.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1808_77925.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____77908)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77894  in
                            mk1 uu____77893  in
                          let uu____77926 =
                            let uu____77927 =
                              let uu____77928 =
                                let uu____77942 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1810_77959 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1810_77959.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1810_77959.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1810_77959.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1810_77959.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1810_77959.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1810_77959.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____77942)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____77928  in
                            mk1 uu____77927  in
                          (nm_rec, uu____77892, uu____77926))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___1817_77964 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___1817_77964.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___1817_77964.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___1817_77964.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___1817_77964.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___1817_77964.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___1820_77966 = env  in
                       let uu____77967 =
                         FStar_TypeChecker_Env.push_bv env.tcenv
                           (let uu___1822_77969 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___1822_77969.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___1822_77969.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         tcenv = uu____77967;
                         subst = (uu___1820_77966.subst);
                         tc_const = (uu___1820_77966.tc_const)
                       }  in
                     let uu____77970 = ensure_m env1 e21  in
                     (match uu____77970 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____77994 =
                              let uu____77995 =
                                let uu____78012 =
                                  let uu____78023 =
                                    let uu____78032 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____78035 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78032, uu____78035)  in
                                  [uu____78023]  in
                                (s_e2, uu____78012)  in
                              FStar_Syntax_Syntax.Tm_app uu____77995  in
                            mk1 uu____77994  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____78077 =
                              let uu____78078 =
                                let uu____78095 =
                                  let uu____78106 =
                                    let uu____78115 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____78115)  in
                                  [uu____78106]  in
                                (s_e1, uu____78095)  in
                              FStar_Syntax_Syntax.Tm_app uu____78078  in
                            mk1 uu____78077  in
                          let uu____78151 =
                            let uu____78152 =
                              let uu____78153 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____78153]  in
                            FStar_Syntax_Util.abs uu____78152 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____78172 =
                            let uu____78173 =
                              let uu____78174 =
                                let uu____78188 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___1834_78205 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___1834_78205.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___1834_78205.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___1834_78205.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___1834_78205.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___1834_78205.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___1834_78205.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____78188)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____78174  in
                            mk1 uu____78173  in
                          ((M t2), uu____78151, uu____78172)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78215 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____78215  in
      let uu____78216 = check env e mn  in
      match uu____78216 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78232 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____78255 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____78255  in
      let uu____78256 = check env e mn  in
      match uu____78256 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____78272 -> failwith "[check_m]: impossible"

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
        (let uu____78305 =
           let uu____78307 = is_C c  in Prims.op_Negation uu____78307  in
         if uu____78305 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____78321 =
           let uu____78322 = FStar_Syntax_Subst.compress c  in
           uu____78322.FStar_Syntax_Syntax.n  in
         match uu____78321 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____78351 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____78351 with
              | (wp_head,wp_args) ->
                  ((let uu____78395 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____78414 =
                           let uu____78416 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____78416
                            in
                         Prims.op_Negation uu____78414)
                       in
                    if uu____78395 then failwith "mismatch" else ());
                   (let uu____78429 =
                      let uu____78430 =
                        let uu____78447 =
                          FStar_List.map2
                            (fun uu____78485  ->
                               fun uu____78486  ->
                                 match (uu____78485, uu____78486) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____78548 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____78548
                                       then "implicit"
                                       else "explicit"  in
                                     ((let uu____78557 =
                                         let uu____78559 =
                                           FStar_Syntax_Util.eq_aqual q q'
                                            in
                                         uu____78559 <>
                                           FStar_Syntax_Util.Equal
                                          in
                                       if uu____78557
                                       then
                                         let uu____78561 =
                                           let uu____78567 =
                                             let uu____78569 =
                                               print_implicit q  in
                                             let uu____78571 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____78569 uu____78571
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____78567)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____78561
                                       else ());
                                      (let uu____78577 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____78577, q)))) args wp_args
                           in
                        (head1, uu____78447)  in
                      FStar_Syntax_Syntax.Tm_app uu____78430  in
                    mk1 uu____78429)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____78623 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____78623 with
              | (binders_orig,comp1) ->
                  let uu____78630 =
                    let uu____78647 =
                      FStar_List.map
                        (fun uu____78687  ->
                           match uu____78687 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____78715 = is_C h  in
                               if uu____78715
                               then
                                 let w' =
                                   let uu____78731 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.op_Hat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____78731
                                    in
                                 let uu____78733 =
                                   let uu____78742 =
                                     let uu____78751 =
                                       let uu____78758 =
                                         let uu____78759 =
                                           let uu____78760 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____78760  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____78759
                                          in
                                       (uu____78758, q)  in
                                     [uu____78751]  in
                                   (w', q) :: uu____78742  in
                                 (w', uu____78733)
                               else
                                 (let x =
                                    let uu____78794 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.op_Hat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____78794
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____78647  in
                  (match uu____78630 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____78868 =
                           let uu____78871 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____78871
                            in
                         FStar_Syntax_Subst.subst_comp uu____78868 comp1  in
                       let app =
                         let uu____78875 =
                           let uu____78876 =
                             let uu____78893 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____78912 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____78913 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____78912, uu____78913)) bvs
                                in
                             (wp, uu____78893)  in
                           FStar_Syntax_Syntax.Tm_app uu____78876  in
                         mk1 uu____78875  in
                       let comp3 =
                         let uu____78928 = type_of_comp comp2  in
                         let uu____78929 = is_monadic_comp comp2  in
                         trans_G env uu____78928 uu____78929 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____78932,uu____78933) ->
             trans_F_ env e wp
         | uu____78974 -> failwith "impossible trans_F_")

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
            let uu____78982 =
              let uu____78983 = star_type' env h  in
              let uu____78986 =
                let uu____78997 =
                  let uu____79006 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____79006)  in
                [uu____78997]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____78983;
                FStar_Syntax_Syntax.effect_args = uu____78986;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____78982
          else
            (let uu____79032 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____79032)

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
    fun t  -> let uu____79053 = n env.tcenv t  in star_type' env uu____79053
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun t  -> let uu____79073 = n env.tcenv t  in check_n env uu____79073
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____79090 = n env.tcenv c  in
        let uu____79091 = n env.tcenv wp  in
        trans_F_ env uu____79090 uu____79091
  