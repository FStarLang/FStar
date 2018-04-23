open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }[@@deriving show]
let __proj__Mkenv__item__env : env -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__env
  
let __proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__subst
  
let __proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__tc_const
  
let empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env
  = fun env  -> fun tc_const  -> { env; subst = []; tc_const } 
let gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts,FStar_Syntax_Syntax.eff_decl)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun binders  ->
      fun a  ->
        fun wp_a  ->
          fun ed  ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.EraseUniverses] env wp_a
               in
            let a1 =
              let uu___77_123 = a  in
              let uu____124 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___77_123.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___77_123.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____124
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____134 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____134
             then
               (d "Elaborating extra WP combinators";
                (let uu____136 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____136))
             else ());
            (let rec collect_binders t =
               let uu____150 =
                 let uu____151 =
                   let uu____154 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____154
                    in
                 uu____151.FStar_Syntax_Syntax.n  in
               match uu____150 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____185) -> t1
                     | uu____194 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____197 = collect_binders rest  in
                   FStar_List.append bs uu____197
               | FStar_Syntax_Syntax.Tm_type uu____208 -> []
               | uu____213 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____233 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____233 FStar_Syntax_Util.name_binders
                in
             (let uu____253 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____253
              then
                let uu____254 =
                  let uu____255 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____255  in
                d uu____254
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____289 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____289 with
                | (sigelt,fv) ->
                    ((let uu____297 =
                        let uu____300 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____300
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____297);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____430  ->
                     match uu____430 with
                     | (t,b) ->
                         let uu____441 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____441))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____474 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____474))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____499 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____499)
                 in
              let uu____500 =
                let uu____517 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____541 =
                        let uu____544 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____544  in
                      FStar_Syntax_Util.arrow gamma uu____541  in
                    let uu____545 =
                      let uu____546 =
                        let uu____553 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____554 =
                          let uu____557 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____557]  in
                        uu____553 :: uu____554  in
                      FStar_List.append binders uu____546  in
                    FStar_Syntax_Util.abs uu____545 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____562 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____563 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____562, uu____563)  in
                match uu____517 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____603 =
                        let uu____604 =
                          let uu____619 =
                            let uu____626 =
                              FStar_List.map
                                (fun uu____646  ->
                                   match uu____646 with
                                   | (bv,uu____656) ->
                                       let uu____657 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____658 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____657, uu____658)) binders
                               in
                            let uu____659 =
                              let uu____666 =
                                let uu____671 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____672 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____671, uu____672)  in
                              let uu____673 =
                                let uu____680 =
                                  let uu____685 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____685)  in
                                [uu____680]  in
                              uu____666 :: uu____673  in
                            FStar_List.append uu____626 uu____659  in
                          (fv, uu____619)  in
                        FStar_Syntax_Syntax.Tm_app uu____604  in
                      mk1 uu____603  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____500 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____750 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____750
                       in
                    let ret1 =
                      let uu____754 =
                        let uu____755 =
                          let uu____758 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____758  in
                        FStar_Syntax_Util.residual_tot uu____755  in
                      FStar_Pervasives_Native.Some uu____754  in
                    let body =
                      let uu____760 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____760 ret1  in
                    let uu____761 =
                      let uu____762 = mk_all_implicit binders  in
                      let uu____769 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____762 uu____769  in
                    FStar_Syntax_Util.abs uu____761 body ret1  in
                  let c_pure1 =
                    let uu____797 = mk_lid "pure"  in
                    register env1 uu____797 c_pure  in
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
                      let uu____802 =
                        let uu____803 =
                          let uu____804 =
                            let uu____811 =
                              let uu____812 =
                                let uu____813 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____813
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____812  in
                            [uu____811]  in
                          let uu____814 =
                            let uu____817 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____817  in
                          FStar_Syntax_Util.arrow uu____804 uu____814  in
                        mk_gctx uu____803  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____802
                       in
                    let r =
                      let uu____819 =
                        let uu____820 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____820  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____819
                       in
                    let ret1 =
                      let uu____824 =
                        let uu____825 =
                          let uu____828 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____828  in
                        FStar_Syntax_Util.residual_tot uu____825  in
                      FStar_Pervasives_Native.Some uu____824  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____836 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____839 =
                          let uu____848 =
                            let uu____851 =
                              let uu____852 =
                                let uu____853 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____853
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____852  in
                            [uu____851]  in
                          FStar_List.append gamma_as_args uu____848  in
                        FStar_Syntax_Util.mk_app uu____836 uu____839  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____856 =
                      let uu____857 = mk_all_implicit binders  in
                      let uu____864 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____857 uu____864  in
                    FStar_Syntax_Util.abs uu____856 outer_body ret1  in
                  let c_app1 =
                    let uu____900 = mk_lid "app"  in
                    register env1 uu____900 c_app  in
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
                      let uu____907 =
                        let uu____914 =
                          let uu____915 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____915  in
                        [uu____914]  in
                      let uu____916 =
                        let uu____919 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____919  in
                      FStar_Syntax_Util.arrow uu____907 uu____916  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____922 =
                        let uu____923 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____923  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____922
                       in
                    let ret1 =
                      let uu____927 =
                        let uu____928 =
                          let uu____931 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____931  in
                        FStar_Syntax_Util.residual_tot uu____928  in
                      FStar_Pervasives_Native.Some uu____927  in
                    let uu____932 =
                      let uu____933 = mk_all_implicit binders  in
                      let uu____940 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____933 uu____940  in
                    let uu____975 =
                      let uu____976 =
                        let uu____985 =
                          let uu____988 =
                            let uu____991 =
                              let uu____1000 =
                                let uu____1003 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1003]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1000
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____991  in
                          let uu____1004 =
                            let uu____1009 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1009]  in
                          uu____988 :: uu____1004  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____985
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____976  in
                    FStar_Syntax_Util.abs uu____932 uu____975 ret1  in
                  let c_lift11 =
                    let uu____1013 = mk_lid "lift1"  in
                    register env1 uu____1013 c_lift1  in
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
                      let uu____1021 =
                        let uu____1028 =
                          let uu____1029 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1029  in
                        let uu____1030 =
                          let uu____1033 =
                            let uu____1034 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1034  in
                          [uu____1033]  in
                        uu____1028 :: uu____1030  in
                      let uu____1035 =
                        let uu____1038 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1038  in
                      FStar_Syntax_Util.arrow uu____1021 uu____1035  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1041 =
                        let uu____1042 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1042  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1041
                       in
                    let a2 =
                      let uu____1044 =
                        let uu____1045 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1045  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1044
                       in
                    let ret1 =
                      let uu____1049 =
                        let uu____1050 =
                          let uu____1053 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1053  in
                        FStar_Syntax_Util.residual_tot uu____1050  in
                      FStar_Pervasives_Native.Some uu____1049  in
                    let uu____1054 =
                      let uu____1055 = mk_all_implicit binders  in
                      let uu____1062 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1055 uu____1062  in
                    let uu____1105 =
                      let uu____1106 =
                        let uu____1115 =
                          let uu____1118 =
                            let uu____1121 =
                              let uu____1130 =
                                let uu____1133 =
                                  let uu____1136 =
                                    let uu____1145 =
                                      let uu____1148 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1148]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1145
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1136
                                   in
                                let uu____1149 =
                                  let uu____1154 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1154]  in
                                uu____1133 :: uu____1149  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1130
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1121  in
                          let uu____1157 =
                            let uu____1162 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1162]  in
                          uu____1118 :: uu____1157  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1115
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1106  in
                    FStar_Syntax_Util.abs uu____1054 uu____1105 ret1  in
                  let c_lift21 =
                    let uu____1166 = mk_lid "lift2"  in
                    register env1 uu____1166 c_lift2  in
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
                      let uu____1173 =
                        let uu____1180 =
                          let uu____1181 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1181  in
                        [uu____1180]  in
                      let uu____1182 =
                        let uu____1185 =
                          let uu____1186 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1186  in
                        FStar_Syntax_Syntax.mk_Total uu____1185  in
                      FStar_Syntax_Util.arrow uu____1173 uu____1182  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1191 =
                        let uu____1192 =
                          let uu____1195 =
                            let uu____1196 =
                              let uu____1203 =
                                let uu____1204 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1204
                                 in
                              [uu____1203]  in
                            let uu____1205 =
                              let uu____1208 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1208  in
                            FStar_Syntax_Util.arrow uu____1196 uu____1205  in
                          mk_ctx uu____1195  in
                        FStar_Syntax_Util.residual_tot uu____1192  in
                      FStar_Pervasives_Native.Some uu____1191  in
                    let e1 =
                      let uu____1210 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1210
                       in
                    let body =
                      let uu____1212 =
                        let uu____1213 =
                          let uu____1220 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1220]  in
                        FStar_List.append gamma uu____1213  in
                      let uu____1225 =
                        let uu____1226 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1229 =
                          let uu____1238 =
                            let uu____1239 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1239  in
                          let uu____1240 = args_of_binders1 gamma  in
                          uu____1238 :: uu____1240  in
                        FStar_Syntax_Util.mk_app uu____1226 uu____1229  in
                      FStar_Syntax_Util.abs uu____1212 uu____1225 ret1  in
                    let uu____1243 =
                      let uu____1244 = mk_all_implicit binders  in
                      let uu____1251 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1244 uu____1251  in
                    FStar_Syntax_Util.abs uu____1243 body ret1  in
                  let c_push1 =
                    let uu____1283 = mk_lid "push"  in
                    register env1 uu____1283 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if
                      (FStar_List.length binders) >
                        (Prims.lift_native_int (0))
                    then
                      let uu____1305 =
                        let uu____1306 =
                          let uu____1321 = args_of_binders1 binders  in
                          (c, uu____1321)  in
                        FStar_Syntax_Syntax.Tm_app uu____1306  in
                      mk1 uu____1305
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1331 =
                        let uu____1332 =
                          let uu____1339 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1340 =
                            let uu____1343 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1343]  in
                          uu____1339 :: uu____1340  in
                        let uu____1344 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1332 uu____1344  in
                      FStar_Syntax_Syntax.mk_Total uu____1331  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1348 =
                      let uu____1349 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1349  in
                    let uu____1360 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.lift_native_int (2)))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1362 =
                        let uu____1365 =
                          let uu____1374 =
                            let uu____1377 =
                              let uu____1380 =
                                let uu____1389 =
                                  let uu____1390 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1390  in
                                [uu____1389]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1380  in
                            [uu____1377]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1374
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1365  in
                      FStar_Syntax_Util.ascribe uu____1362
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1348 uu____1360
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1410 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1410 wp_if_then_else  in
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
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.lift_native_int (1)))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1421 =
                        let uu____1430 =
                          let uu____1433 =
                            let uu____1436 =
                              let uu____1445 =
                                let uu____1448 =
                                  let uu____1451 =
                                    let uu____1460 =
                                      let uu____1461 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1461
                                       in
                                    [uu____1460]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1451
                                   in
                                [uu____1448]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1445
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1436  in
                          let uu____1466 =
                            let uu____1471 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1471]  in
                          uu____1433 :: uu____1466  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1430
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1421  in
                    let uu____1474 =
                      let uu____1475 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1475  in
                    FStar_Syntax_Util.abs uu____1474 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1487 = mk_lid "wp_assert"  in
                    register env1 uu____1487 wp_assert  in
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
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.lift_native_int (1)))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1498 =
                        let uu____1507 =
                          let uu____1510 =
                            let uu____1513 =
                              let uu____1522 =
                                let uu____1525 =
                                  let uu____1528 =
                                    let uu____1537 =
                                      let uu____1538 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1538
                                       in
                                    [uu____1537]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1528
                                   in
                                [uu____1525]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1522
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1513  in
                          let uu____1543 =
                            let uu____1548 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1548]  in
                          uu____1510 :: uu____1543  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1507
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1498  in
                    let uu____1551 =
                      let uu____1552 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1552  in
                    FStar_Syntax_Util.abs uu____1551 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1564 = mk_lid "wp_assume"  in
                    register env1 uu____1564 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1573 =
                        let uu____1580 =
                          let uu____1581 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1581  in
                        [uu____1580]  in
                      let uu____1582 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1573 uu____1582  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1589 =
                        let uu____1598 =
                          let uu____1601 =
                            let uu____1604 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1604  in
                          let uu____1613 =
                            let uu____1618 =
                              let uu____1621 =
                                let uu____1630 =
                                  let uu____1633 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1633]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1630
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1621  in
                            [uu____1618]  in
                          uu____1601 :: uu____1613  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1598
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1589  in
                    let uu____1640 =
                      let uu____1641 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1641  in
                    FStar_Syntax_Util.abs uu____1640 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1653 = mk_lid "wp_close"  in
                    register env1 uu____1653 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____1663 =
                      let uu____1664 =
                        let uu____1665 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1665
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1664  in
                    FStar_Pervasives_Native.Some uu____1663  in
                  let mk_forall1 x body =
                    let uu____1681 =
                      let uu____1688 =
                        let uu____1689 =
                          let uu____1704 =
                            let uu____1707 =
                              let uu____1708 =
                                let uu____1709 =
                                  let uu____1710 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1710]  in
                                FStar_Syntax_Util.abs uu____1709 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1708  in
                            [uu____1707]  in
                          (FStar_Syntax_Util.tforall, uu____1704)  in
                        FStar_Syntax_Syntax.Tm_app uu____1689  in
                      FStar_Syntax_Syntax.mk uu____1688  in
                    uu____1681 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____1722 =
                      let uu____1723 = FStar_Syntax_Subst.compress t  in
                      uu____1723.FStar_Syntax_Syntax.n  in
                    match uu____1722 with
                    | FStar_Syntax_Syntax.Tm_type uu____1726 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1752  ->
                              match uu____1752 with
                              | (b,uu____1758) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1759 -> true  in
                  let rec is_monotonic t =
                    let uu____1766 =
                      let uu____1767 = FStar_Syntax_Subst.compress t  in
                      uu____1767.FStar_Syntax_Syntax.n  in
                    match uu____1766 with
                    | FStar_Syntax_Syntax.Tm_type uu____1770 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1796  ->
                              match uu____1796 with
                              | (b,uu____1802) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1803 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____1869 =
                      let uu____1870 = FStar_Syntax_Subst.compress t1  in
                      uu____1870.FStar_Syntax_Syntax.n  in
                    match uu____1869 with
                    | FStar_Syntax_Syntax.Tm_type uu____1873 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1876);
                                      FStar_Syntax_Syntax.pos = uu____1877;
                                      FStar_Syntax_Syntax.vars = uu____1878;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1912 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1912
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____1915 =
                              let uu____1918 =
                                let uu____1927 =
                                  let uu____1928 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1928  in
                                [uu____1927]  in
                              FStar_Syntax_Util.mk_app x uu____1918  in
                            let uu____1929 =
                              let uu____1932 =
                                let uu____1941 =
                                  let uu____1942 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1942  in
                                [uu____1941]  in
                              FStar_Syntax_Util.mk_app y uu____1932  in
                            mk_rel1 b uu____1915 uu____1929  in
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
                             let uu____1947 =
                               let uu____1948 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1951 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1948 uu____1951  in
                             let uu____1954 =
                               let uu____1955 =
                                 let uu____1958 =
                                   let uu____1967 =
                                     let uu____1968 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1968
                                      in
                                   [uu____1967]  in
                                 FStar_Syntax_Util.mk_app x uu____1958  in
                               let uu____1969 =
                                 let uu____1972 =
                                   let uu____1981 =
                                     let uu____1982 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1982
                                      in
                                   [uu____1981]  in
                                 FStar_Syntax_Util.mk_app y uu____1972  in
                               mk_rel1 b uu____1955 uu____1969  in
                             FStar_Syntax_Util.mk_imp uu____1947 uu____1954
                              in
                           let uu____1983 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1983)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1986);
                                      FStar_Syntax_Syntax.pos = uu____1987;
                                      FStar_Syntax_Syntax.vars = uu____1988;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2022 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2022
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2025 =
                              let uu____2028 =
                                let uu____2037 =
                                  let uu____2038 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2038  in
                                [uu____2037]  in
                              FStar_Syntax_Util.mk_app x uu____2028  in
                            let uu____2039 =
                              let uu____2042 =
                                let uu____2051 =
                                  let uu____2052 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2052  in
                                [uu____2051]  in
                              FStar_Syntax_Util.mk_app y uu____2042  in
                            mk_rel1 b uu____2025 uu____2039  in
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
                             let uu____2057 =
                               let uu____2058 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2061 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2058 uu____2061  in
                             let uu____2064 =
                               let uu____2065 =
                                 let uu____2068 =
                                   let uu____2077 =
                                     let uu____2078 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2078
                                      in
                                   [uu____2077]  in
                                 FStar_Syntax_Util.mk_app x uu____2068  in
                               let uu____2079 =
                                 let uu____2082 =
                                   let uu____2091 =
                                     let uu____2092 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2092
                                      in
                                   [uu____2091]  in
                                 FStar_Syntax_Util.mk_app y uu____2082  in
                               mk_rel1 b uu____2065 uu____2079  in
                             FStar_Syntax_Util.mk_imp uu____2057 uu____2064
                              in
                           let uu____2093 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2093)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___78_2124 = t1  in
                          let uu____2125 =
                            let uu____2126 =
                              let uu____2139 =
                                let uu____2140 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2140  in
                              ([binder], uu____2139)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2126  in
                          {
                            FStar_Syntax_Syntax.n = uu____2125;
                            FStar_Syntax_Syntax.pos =
                              (uu___78_2124.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___78_2124.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2155 ->
                        failwith "unhandled arrow"
                    | uu____2168 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                          [FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.UnfoldUntil
                            FStar_Syntax_Syntax.Delta_constant] env1 t
                         in
                      let uu____2189 =
                        let uu____2190 = FStar_Syntax_Subst.compress t1  in
                        uu____2190.FStar_Syntax_Syntax.n  in
                      match uu____2189 with
                      | FStar_Syntax_Syntax.Tm_type uu____2193 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2216 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____2216
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2235 =
                                let uu____2236 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2236 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2235
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.lift_native_int (1)))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2263 =
                            let uu____2270 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2284  ->
                                     match uu____2284 with
                                     | (t2,q) ->
                                         let uu____2291 = project i x  in
                                         let uu____2292 = project i y  in
                                         mk_stronger t2 uu____2291 uu____2292)
                                args
                               in
                            match uu____2270 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2263 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2319);
                                      FStar_Syntax_Syntax.pos = uu____2320;
                                      FStar_Syntax_Syntax.vars = uu____2321;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2359  ->
                                   match uu____2359 with
                                   | (bv,q) ->
                                       let uu____2366 =
                                         let uu____2367 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2367  in
                                       FStar_Syntax_Syntax.gen_bv uu____2366
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2374 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2374) bvs
                             in
                          let body =
                            let uu____2376 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2377 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2376 uu____2377  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2384);
                                      FStar_Syntax_Syntax.pos = uu____2385;
                                      FStar_Syntax_Syntax.vars = uu____2386;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2424  ->
                                   match uu____2424 with
                                   | (bv,q) ->
                                       let uu____2431 =
                                         let uu____2432 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2432  in
                                       FStar_Syntax_Syntax.gen_bv uu____2431
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2439 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2439) bvs
                             in
                          let body =
                            let uu____2441 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2442 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2441 uu____2442  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2447 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____2449 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____2450 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____2451 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____2449 uu____2450 uu____2451  in
                    let uu____2452 =
                      let uu____2453 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____2453  in
                    FStar_Syntax_Util.abs uu____2452 body ret_tot_type  in
                  let stronger1 =
                    let uu____2481 = mk_lid "stronger"  in
                    register env1 uu____2481 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2487 = FStar_Util.prefix gamma  in
                    match uu____2487 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____2532 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2532
                             in
                          let uu____2535 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____2535 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2545 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____2545  in
                              let guard_free1 =
                                let uu____2555 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____2555  in
                              let pat =
                                let uu____2559 =
                                  let uu____2568 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____2568]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2559
                                 in
                              let pattern_guarded_body =
                                let uu____2572 =
                                  let uu____2573 =
                                    let uu____2580 =
                                      let uu____2581 =
                                        let uu____2592 =
                                          let uu____2595 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____2595]  in
                                        [uu____2592]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2581
                                       in
                                    (body, uu____2580)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____2573  in
                                mk1 uu____2572  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2600 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____2604 =
                            let uu____2605 =
                              let uu____2606 =
                                let uu____2607 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____2610 =
                                  let uu____2619 = args_of_binders1 wp_args
                                     in
                                  let uu____2622 =
                                    let uu____2625 =
                                      let uu____2626 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____2626
                                       in
                                    [uu____2625]  in
                                  FStar_List.append uu____2619 uu____2622  in
                                FStar_Syntax_Util.mk_app uu____2607
                                  uu____2610
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2606  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2605
                             in
                          FStar_Syntax_Util.abs gamma uu____2604
                            ret_gtot_type
                           in
                        let uu____2627 =
                          let uu____2628 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____2628  in
                        FStar_Syntax_Util.abs uu____2627 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____2640 = mk_lid "wp_ite"  in
                    register env1 uu____2640 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2646 = FStar_Util.prefix gamma  in
                    match uu____2646 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____2689 =
                            let uu____2690 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____2693 =
                              let uu____2702 =
                                let uu____2703 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____2703  in
                              [uu____2702]  in
                            FStar_Syntax_Util.mk_app uu____2690 uu____2693
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2689
                           in
                        let uu____2704 =
                          let uu____2705 =
                            let uu____2712 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____2712 gamma  in
                          FStar_List.append binders uu____2705  in
                        FStar_Syntax_Util.abs uu____2704 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____2728 = mk_lid "null_wp"  in
                    register env1 uu____2728 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____2737 =
                        let uu____2746 =
                          let uu____2749 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____2750 =
                            let uu____2753 =
                              let uu____2756 =
                                let uu____2765 =
                                  let uu____2766 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____2766  in
                                [uu____2765]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2756
                               in
                            let uu____2767 =
                              let uu____2772 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____2772]  in
                            uu____2753 :: uu____2767  in
                          uu____2749 :: uu____2750  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2746
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____2737  in
                    let uu____2775 =
                      let uu____2776 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____2776  in
                    FStar_Syntax_Util.abs uu____2775 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____2788 = mk_lid "wp_trivial"  in
                    register env1 uu____2788 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____2793 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____2793
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____2800 =
                      let uu____2803 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____2803  in
                    let uu____2855 =
                      let uu___79_2856 = ed  in
                      let uu____2857 =
                        let uu____2858 = c wp_if_then_else2  in
                        ([], uu____2858)  in
                      let uu____2861 =
                        let uu____2862 = c wp_ite2  in ([], uu____2862)  in
                      let uu____2865 =
                        let uu____2866 = c stronger2  in ([], uu____2866)  in
                      let uu____2869 =
                        let uu____2870 = c wp_close2  in ([], uu____2870)  in
                      let uu____2873 =
                        let uu____2874 = c wp_assert2  in ([], uu____2874)
                         in
                      let uu____2877 =
                        let uu____2878 = c wp_assume2  in ([], uu____2878)
                         in
                      let uu____2881 =
                        let uu____2882 = c null_wp2  in ([], uu____2882)  in
                      let uu____2885 =
                        let uu____2886 = c wp_trivial2  in ([], uu____2886)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___79_2856.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___79_2856.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___79_2856.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___79_2856.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___79_2856.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___79_2856.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___79_2856.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2857;
                        FStar_Syntax_Syntax.ite_wp = uu____2861;
                        FStar_Syntax_Syntax.stronger = uu____2865;
                        FStar_Syntax_Syntax.close_wp = uu____2869;
                        FStar_Syntax_Syntax.assert_p = uu____2873;
                        FStar_Syntax_Syntax.assume_p = uu____2877;
                        FStar_Syntax_Syntax.null_wp = uu____2881;
                        FStar_Syntax_Syntax.trivial = uu____2885;
                        FStar_Syntax_Syntax.repr =
                          (uu___79_2856.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___79_2856.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___79_2856.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___79_2856.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___79_2856.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____2800, uu____2855)))))
  
type env_ = env[@@deriving show]
let get_env : env -> FStar_TypeChecker_Env.env = fun env  -> env.env 
let set_env : env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___80_2906 = dmff_env  in
      {
        env = env';
        subst = (uu___80_2906.subst);
        tc_const = (uu___80_2906.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let uu___is_N : nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2923 -> false 
let __proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0 
let uu___is_M : nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2937 -> false 
let __proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let nm_of_comp : FStar_Syntax_Syntax.comp' -> nm =
  fun uu___66_2949  ->
    match uu___66_2949 with
    | FStar_Syntax_Syntax.Total (t,uu____2951) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___65_2964  ->
                match uu___65_2964 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2965 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2967 =
          let uu____2968 =
            let uu____2969 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2969
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2968  in
        failwith uu____2967
    | FStar_Syntax_Syntax.GTotal uu____2970 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let string_of_nm : nm -> Prims.string =
  fun uu___67_2983  ->
    match uu___67_2983 with
    | N t ->
        let uu____2985 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2985
    | M t ->
        let uu____2987 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2987
  
let is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2993,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2995;
                      FStar_Syntax_Syntax.vars = uu____2996;_})
        -> nm_of_comp n2
    | uu____3013 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____3023 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____3023 with | M uu____3024 -> true | N uu____3025 -> false
  
exception Not_found 
let uu___is_Not_found : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3031 -> false
  
let double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ  ->
    let star_once typ1 =
      let uu____3045 =
        let uu____3052 =
          let uu____3053 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3053  in
        [uu____3052]  in
      let uu____3054 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3045 uu____3054  in
    let uu____3057 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3057
  
let rec mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun mk1  ->
    fun env  ->
      fun a  ->
        let uu____3102 =
          let uu____3103 =
            let uu____3116 =
              let uu____3123 =
                let uu____3128 =
                  let uu____3129 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____3129  in
                let uu____3130 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____3128, uu____3130)  in
              [uu____3123]  in
            let uu____3139 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____3116, uu____3139)  in
          FStar_Syntax_Syntax.Tm_arrow uu____3103  in
        mk1 uu____3102

and star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3173) ->
          let binders1 =
            FStar_List.map
              (fun uu____3209  ->
                 match uu____3209 with
                 | (bv,aqual) ->
                     let uu____3220 =
                       let uu___81_3221 = bv  in
                       let uu____3222 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___81_3221.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___81_3221.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3222
                       }  in
                     (uu____3220, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3225,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3227);
                             FStar_Syntax_Syntax.pos = uu____3228;
                             FStar_Syntax_Syntax.vars = uu____3229;_})
               ->
               let uu____3254 =
                 let uu____3255 =
                   let uu____3268 =
                     let uu____3269 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3269  in
                   (binders1, uu____3268)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3255  in
               mk1 uu____3254
           | uu____3276 ->
               let uu____3277 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3277 with
                | N hn ->
                    let uu____3279 =
                      let uu____3280 =
                        let uu____3293 =
                          let uu____3294 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3294  in
                        (binders1, uu____3293)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3280  in
                    mk1 uu____3279
                | M a ->
                    let uu____3302 =
                      let uu____3303 =
                        let uu____3316 =
                          let uu____3323 =
                            let uu____3330 =
                              let uu____3335 =
                                let uu____3336 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____3336  in
                              let uu____3337 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____3335, uu____3337)  in
                            [uu____3330]  in
                          FStar_List.append binders1 uu____3323  in
                        let uu____3350 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____3316, uu____3350)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3303  in
                    mk1 uu____3302))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3428 = f x  in
                    FStar_Util.string_builder_append strb uu____3428);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3435 = f x1  in
                         FStar_Util.string_builder_append strb uu____3435))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____3437 =
              let uu____3442 =
                let uu____3443 = FStar_Syntax_Print.term_to_string t2  in
                let uu____3444 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3443 uu____3444
                 in
              (FStar_Errors.Warning_DependencyFound, uu____3442)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3437  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3456 =
              let uu____3457 = FStar_Syntax_Subst.compress ty  in
              uu____3457.FStar_Syntax_Syntax.n  in
            match uu____3456 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3478 =
                  let uu____3479 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____3479  in
                if uu____3478
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3509 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____3509 s  in
                       let uu____3512 =
                         let uu____3513 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____3513  in
                       if uu____3512
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____3516 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____3516 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3538  ->
                                  match uu____3538 with
                                  | (bv,uu____3548) ->
                                      (non_dependent_or_raise s
                                         bv.FStar_Syntax_Syntax.sort;
                                       FStar_Util.set_add bv s))
                             FStar_Syntax_Syntax.no_names binders1
                            in
                         let ct = FStar_Syntax_Util.comp_result c1  in
                         (non_dependent_or_raise s ct;
                          (let k = n1 - (FStar_List.length binders1)  in
                           if k > (Prims.lift_native_int (0))
                           then is_non_dependent_arrow ct k
                           else true))
                   with | Not_found  -> false)
            | uu____3562 ->
                ((let uu____3564 =
                    let uu____3569 =
                      let uu____3570 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3570
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3569)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3564);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____3577 =
              let uu____3578 = FStar_Syntax_Subst.compress head2  in
              uu____3578.FStar_Syntax_Syntax.n  in
            match uu____3577 with
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
                  (let uu____3583 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____3583)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3585 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____3585 with
                 | ((uu____3594,ty),uu____3596) ->
                     let uu____3601 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____3601
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1
                          in
                       let uu____3609 =
                         let uu____3610 = FStar_Syntax_Subst.compress res  in
                         uu____3610.FStar_Syntax_Syntax.n  in
                       (match uu____3609 with
                        | FStar_Syntax_Syntax.Tm_app uu____3613 -> true
                        | uu____3628 ->
                            ((let uu____3630 =
                                let uu____3635 =
                                  let uu____3636 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3636
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3635)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3630);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3638 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3639 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3641) ->
                is_valid_application t2
            | uu____3646 -> false  in
          let uu____3647 = is_valid_application head1  in
          if uu____3647
          then
            let uu____3648 =
              let uu____3649 =
                let uu____3664 =
                  FStar_List.map
                    (fun uu____3685  ->
                       match uu____3685 with
                       | (t2,qual) ->
                           let uu____3702 = star_type' env t2  in
                           (uu____3702, qual)) args
                   in
                (head1, uu____3664)  in
              FStar_Syntax_Syntax.Tm_app uu____3649  in
            mk1 uu____3648
          else
            (let uu____3712 =
               let uu____3717 =
                 let uu____3718 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3718
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____3717)  in
             FStar_Errors.raise_err uu____3712)
      | FStar_Syntax_Syntax.Tm_bvar uu____3719 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3720 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3721 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3722 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3746 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____3746 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___84_3754 = env  in
                 let uu____3755 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____3755;
                   subst = (uu___84_3754.subst);
                   tc_const = (uu___84_3754.tc_const)
                 }  in
               let repr2 = star_type' env1 repr1  in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x,t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x  in
          let sort = star_type' env x1.FStar_Syntax_Syntax.sort  in
          let subst1 =
            [FStar_Syntax_Syntax.DB ((Prims.lift_native_int (0)), x1)]  in
          let t3 = FStar_Syntax_Subst.subst subst1 t2  in
          let t4 = star_type' env t3  in
          let subst2 =
            [FStar_Syntax_Syntax.NM (x1, (Prims.lift_native_int (0)))]  in
          let t5 = FStar_Syntax_Subst.subst subst2 t4  in
          mk1
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___85_3775 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___85_3775.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___85_3775.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3782 =
            let uu____3783 =
              let uu____3790 = star_type' env t2  in (uu____3790, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____3783  in
          mk1 uu____3782
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3838 =
            let uu____3839 =
              let uu____3866 = star_type' env e  in
              let uu____3867 =
                let uu____3882 =
                  let uu____3889 = star_type' env t2  in
                  FStar_Util.Inl uu____3889  in
                (uu____3882, FStar_Pervasives_Native.None)  in
              (uu____3866, uu____3867, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3839  in
          mk1 uu____3838
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3967 =
            let uu____3968 =
              let uu____3995 = star_type' env e  in
              let uu____3996 =
                let uu____4011 =
                  let uu____4018 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____4018  in
                (uu____4011, FStar_Pervasives_Native.None)  in
              (uu____3995, uu____3996, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3968  in
          mk1 uu____3967
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4049,(uu____4050,FStar_Pervasives_Native.Some uu____4051),uu____4052)
          ->
          let uu____4101 =
            let uu____4106 =
              let uu____4107 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4107
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4106)  in
          FStar_Errors.raise_err uu____4101
      | FStar_Syntax_Syntax.Tm_refine uu____4108 ->
          let uu____4115 =
            let uu____4120 =
              let uu____4121 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4121
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4120)  in
          FStar_Errors.raise_err uu____4115
      | FStar_Syntax_Syntax.Tm_uinst uu____4122 ->
          let uu____4129 =
            let uu____4134 =
              let uu____4135 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4135
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4134)  in
          FStar_Errors.raise_err uu____4129
      | FStar_Syntax_Syntax.Tm_quoted uu____4136 ->
          let uu____4143 =
            let uu____4148 =
              let uu____4149 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4149
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4148)  in
          FStar_Errors.raise_err uu____4143
      | FStar_Syntax_Syntax.Tm_constant uu____4150 ->
          let uu____4151 =
            let uu____4156 =
              let uu____4157 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4157
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4156)  in
          FStar_Errors.raise_err uu____4151
      | FStar_Syntax_Syntax.Tm_match uu____4158 ->
          let uu____4181 =
            let uu____4186 =
              let uu____4187 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4187
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4186)  in
          FStar_Errors.raise_err uu____4181
      | FStar_Syntax_Syntax.Tm_let uu____4188 ->
          let uu____4201 =
            let uu____4206 =
              let uu____4207 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4207
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4206)  in
          FStar_Errors.raise_err uu____4201
      | FStar_Syntax_Syntax.Tm_uvar uu____4208 ->
          let uu____4225 =
            let uu____4230 =
              let uu____4231 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4231
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4230)  in
          FStar_Errors.raise_err uu____4225
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4232 =
            let uu____4237 =
              let uu____4238 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4238
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4237)  in
          FStar_Errors.raise_err uu____4232
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4240 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____4240
      | FStar_Syntax_Syntax.Tm_delayed uu____4243 -> failwith "impossible"

let is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___69_4274  ->
    match uu___69_4274 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___68_4281  ->
                match uu___68_4281 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4282 -> false))
  
let rec is_C : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____4288 =
      let uu____4289 = FStar_Syntax_Subst.compress t  in
      uu____4289.FStar_Syntax_Syntax.n  in
    match uu____4288 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4315 =
            let uu____4316 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____4316  in
          is_C uu____4315  in
        if r
        then
          ((let uu____4332 =
              let uu____4333 =
                FStar_List.for_all
                  (fun uu____4341  ->
                     match uu____4341 with | (h,uu____4347) -> is_C h) args
                 in
              Prims.op_Negation uu____4333  in
            if uu____4332 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4351 =
              let uu____4352 =
                FStar_List.for_all
                  (fun uu____4361  ->
                     match uu____4361 with
                     | (h,uu____4367) ->
                         let uu____4368 = is_C h  in
                         Prims.op_Negation uu____4368) args
                 in
              Prims.op_Negation uu____4352  in
            if uu____4351 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4388 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____4388 with
         | M t1 ->
             ((let uu____4391 = is_C t1  in
               if uu____4391 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4395) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4401) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4407,uu____4408) -> is_C t1
    | uu____4449 -> false
  
let mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
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
          let uu____4480 =
            let uu____4481 =
              let uu____4496 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____4497 =
                let uu____4504 =
                  let uu____4509 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____4509)  in
                [uu____4504]  in
              (uu____4496, uu____4497)  in
            FStar_Syntax_Syntax.Tm_app uu____4481  in
          mk1 uu____4480  in
        let uu____4524 =
          let uu____4525 = FStar_Syntax_Syntax.mk_binder p  in [uu____4525]
           in
        FStar_Syntax_Util.abs uu____4524 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___70_4530  ->
    match uu___70_4530 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4531 -> false
  
let rec check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm ->
        (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____4764 =
          match uu____4764 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4795 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4797 =
                       let uu____4798 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____4798  in
                     Prims.op_Negation uu____4797)
                   in
                if uu____4795
                then
                  let uu____4799 =
                    let uu____4804 =
                      let uu____4805 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____4806 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____4807 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4805 uu____4806 uu____4807
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4804)  in
                  FStar_Errors.raise_err uu____4799
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4824 = mk_return env t1 s_e  in
                     ((M t1), uu____4824, u_e)))
               | (M t1,N t2) ->
                   let uu____4827 =
                     let uu____4832 =
                       let uu____4833 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____4834 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____4835 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4833 uu____4834 uu____4835
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4832)
                      in
                   FStar_Errors.raise_err uu____4827)
           in
        let ensure_m env1 e2 =
          let strip_m uu___71_4882 =
            match uu___71_4882 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4898 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____4918 =
                let uu____4923 =
                  let uu____4924 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4924
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4923)  in
              FStar_Errors.raise_error uu____4918 e2.FStar_Syntax_Syntax.pos
          | M uu____4931 ->
              let uu____4932 = check env1 e2 context_nm  in
              strip_m uu____4932
           in
        let uu____4939 =
          let uu____4940 = FStar_Syntax_Subst.compress e  in
          uu____4940.FStar_Syntax_Syntax.n  in
        match uu____4939 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4949 ->
            let uu____4950 = infer env e  in return_if uu____4950
        | FStar_Syntax_Syntax.Tm_name uu____4957 ->
            let uu____4958 = infer env e  in return_if uu____4958
        | FStar_Syntax_Syntax.Tm_fvar uu____4965 ->
            let uu____4966 = infer env e  in return_if uu____4966
        | FStar_Syntax_Syntax.Tm_abs uu____4973 ->
            let uu____4990 = infer env e  in return_if uu____4990
        | FStar_Syntax_Syntax.Tm_constant uu____4997 ->
            let uu____4998 = infer env e  in return_if uu____4998
        | FStar_Syntax_Syntax.Tm_quoted uu____5005 ->
            let uu____5012 = infer env e  in return_if uu____5012
        | FStar_Syntax_Syntax.Tm_app uu____5019 ->
            let uu____5034 = infer env e  in return_if uu____5034
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5042 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____5042 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5104) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5110) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5116,uu____5117) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5158 ->
            let uu____5171 =
              let uu____5172 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5172  in
            failwith uu____5171
        | FStar_Syntax_Syntax.Tm_type uu____5179 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5186 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5205 ->
            let uu____5212 =
              let uu____5213 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5213  in
            failwith uu____5212
        | FStar_Syntax_Syntax.Tm_uvar uu____5220 ->
            let uu____5237 =
              let uu____5238 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5238  in
            failwith uu____5237
        | FStar_Syntax_Syntax.Tm_delayed uu____5245 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5276 =
              let uu____5277 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5277  in
            failwith uu____5276

and infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mk1 x =
        FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
          e.FStar_Syntax_Syntax.pos
         in
      let normalize1 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses] env.env
         in
      let uu____5305 =
        let uu____5306 = FStar_Syntax_Subst.compress e  in
        uu____5306.FStar_Syntax_Syntax.n  in
      match uu____5305 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5324 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____5324
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5371;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5372;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5378 =
                  let uu___86_5379 = rc  in
                  let uu____5380 =
                    let uu____5385 =
                      let uu____5386 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____5386  in
                    FStar_Pervasives_Native.Some uu____5385  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___86_5379.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5380;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___86_5379.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____5378
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___87_5396 = env  in
            let uu____5397 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____5397;
              subst = (uu___87_5396.subst);
              tc_const = (uu___87_5396.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____5417  ->
                 match uu____5417 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___88_5430 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___88_5430.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___88_5430.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____5431 =
            FStar_List.fold_left
              (fun uu____5460  ->
                 fun uu____5461  ->
                   match (uu____5460, uu____5461) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____5509 = is_C c  in
                       if uu____5509
                       then
                         let xw =
                           let uu____5517 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5517
                            in
                         let x =
                           let uu___89_5519 = bv  in
                           let uu____5520 =
                             let uu____5523 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____5523  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___89_5519.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___89_5519.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5520
                           }  in
                         let env3 =
                           let uu___90_5525 = env2  in
                           let uu____5526 =
                             let uu____5529 =
                               let uu____5530 =
                                 let uu____5537 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____5537)  in
                               FStar_Syntax_Syntax.NT uu____5530  in
                             uu____5529 :: (env2.subst)  in
                           {
                             env = (uu___90_5525.env);
                             subst = uu____5526;
                             tc_const = (uu___90_5525.tc_const)
                           }  in
                         let uu____5538 =
                           let uu____5541 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____5542 =
                             let uu____5545 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____5545 :: acc  in
                           uu____5541 :: uu____5542  in
                         (env3, uu____5538)
                       else
                         (let x =
                            let uu___91_5550 = bv  in
                            let uu____5551 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___91_5550.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___91_5550.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5551
                            }  in
                          let uu____5554 =
                            let uu____5557 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____5557 :: acc  in
                          (env2, uu____5554))) (env1, []) binders1
             in
          (match uu____5431 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____5577 =
                 let check_what =
                   let uu____5599 = is_monadic rc_opt1  in
                   if uu____5599 then check_m else check_n  in
                 let uu____5613 = check_what env2 body1  in
                 match uu____5613 with
                 | (t,s_body,u_body) ->
                     let uu____5629 =
                       let uu____5630 =
                         let uu____5631 = is_monadic rc_opt1  in
                         if uu____5631 then M t else N t  in
                       comp_of_nm uu____5630  in
                     (uu____5629, s_body, u_body)
                  in
               (match uu____5577 with
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
                                 let uu____5656 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___72_5660  ->
                                           match uu___72_5660 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5661 -> false))
                                    in
                                 if uu____5656
                                 then
                                   let uu____5662 =
                                     FStar_List.filter
                                       (fun uu___73_5666  ->
                                          match uu___73_5666 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5667 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5662
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5676 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___74_5680  ->
                                         match uu___74_5680 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5681 -> false))
                                  in
                               if uu____5676
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___75_5688  ->
                                        match uu___75_5688 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5689 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____5690 =
                                   let uu____5691 =
                                     let uu____5696 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____5696
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5691 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____5690
                               else
                                 (let uu____5698 =
                                    let uu___92_5699 = rc  in
                                    let uu____5700 =
                                      let uu____5705 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____5705
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___92_5699.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5700;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___92_5699.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____5698))
                       in
                    let uu____5706 =
                      let comp1 =
                        let uu____5716 = is_monadic rc_opt1  in
                        let uu____5717 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5716 uu____5717
                         in
                      let uu____5718 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____5718,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____5706 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____5760 =
                             let uu____5761 =
                               let uu____5778 =
                                 let uu____5781 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____5781 s_rc_opt  in
                               (s_binders1, s_body1, uu____5778)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5761  in
                           mk1 uu____5760  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____5791 =
                             let uu____5792 =
                               let uu____5809 =
                                 let uu____5812 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____5812 u_rc_opt  in
                               (u_binders2, u_body2, uu____5809)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5792  in
                           mk1 uu____5791  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5822;_};
            FStar_Syntax_Syntax.fv_delta = uu____5823;
            FStar_Syntax_Syntax.fv_qual = uu____5824;_}
          ->
          let uu____5827 =
            let uu____5832 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5832  in
          (match uu____5827 with
           | (uu____5863,t) ->
               let uu____5865 =
                 let uu____5866 = normalize1 t  in N uu____5866  in
               (uu____5865, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5867;
             FStar_Syntax_Syntax.vars = uu____5868;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5931 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5931 with
           | (unary_op,uu____5953) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6012;
             FStar_Syntax_Syntax.vars = uu____6013;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6089 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6089 with
           | (unary_op,uu____6111) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6176;
             FStar_Syntax_Syntax.vars = uu____6177;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____6215 = infer env a  in
          (match uu____6215 with
           | (t,s,u) ->
               let uu____6231 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6231 with
                | (head1,uu____6253) ->
                    let uu____6274 =
                      let uu____6275 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____6275  in
                    let uu____6276 =
                      let uu____6279 =
                        let uu____6280 =
                          let uu____6295 =
                            let uu____6298 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6298]  in
                          (head1, uu____6295)  in
                        FStar_Syntax_Syntax.Tm_app uu____6280  in
                      mk1 uu____6279  in
                    let uu____6303 =
                      let uu____6306 =
                        let uu____6307 =
                          let uu____6322 =
                            let uu____6325 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6325]  in
                          (head1, uu____6322)  in
                        FStar_Syntax_Syntax.Tm_app uu____6307  in
                      mk1 uu____6306  in
                    (uu____6274, uu____6276, uu____6303)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6334;
             FStar_Syntax_Syntax.vars = uu____6335;_},(a1,uu____6337)::a2::[])
          ->
          let uu____6379 = infer env a1  in
          (match uu____6379 with
           | (t,s,u) ->
               let uu____6395 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6395 with
                | (head1,uu____6417) ->
                    let uu____6438 =
                      let uu____6441 =
                        let uu____6442 =
                          let uu____6457 =
                            let uu____6460 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6460; a2]  in
                          (head1, uu____6457)  in
                        FStar_Syntax_Syntax.Tm_app uu____6442  in
                      mk1 uu____6441  in
                    let uu____6477 =
                      let uu____6480 =
                        let uu____6481 =
                          let uu____6496 =
                            let uu____6499 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6499; a2]  in
                          (head1, uu____6496)  in
                        FStar_Syntax_Syntax.Tm_app uu____6481  in
                      mk1 uu____6480  in
                    (t, uu____6438, uu____6477)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6520;
             FStar_Syntax_Syntax.vars = uu____6521;_},uu____6522)
          ->
          let uu____6543 =
            let uu____6548 =
              let uu____6549 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6549
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6548)  in
          FStar_Errors.raise_error uu____6543 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6556;
             FStar_Syntax_Syntax.vars = uu____6557;_},uu____6558)
          ->
          let uu____6579 =
            let uu____6584 =
              let uu____6585 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6585
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6584)  in
          FStar_Errors.raise_error uu____6579 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6614 = check_n env head1  in
          (match uu____6614 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6636 =
                   let uu____6637 = FStar_Syntax_Subst.compress t  in
                   uu____6637.FStar_Syntax_Syntax.n  in
                 match uu____6636 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6640 -> true
                 | uu____6653 -> false  in
               let rec flatten1 t =
                 let uu____6672 =
                   let uu____6673 = FStar_Syntax_Subst.compress t  in
                   uu____6673.FStar_Syntax_Syntax.n  in
                 match uu____6672 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6690);
                                FStar_Syntax_Syntax.pos = uu____6691;
                                FStar_Syntax_Syntax.vars = uu____6692;_})
                     when is_arrow t1 ->
                     let uu____6717 = flatten1 t1  in
                     (match uu____6717 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6799,uu____6800)
                     -> flatten1 e1
                 | uu____6841 ->
                     let uu____6842 =
                       let uu____6847 =
                         let uu____6848 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6848
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6847)  in
                     FStar_Errors.raise_err uu____6842
                  in
               let uu____6861 = flatten1 t_head  in
               (match uu____6861 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6921 =
                          let uu____6926 =
                            let uu____6927 = FStar_Util.string_of_int n1  in
                            let uu____6934 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____6945 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6927 uu____6934 uu____6945
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6926)
                           in
                        FStar_Errors.raise_err uu____6921)
                     else ();
                     (let uu____6953 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____6953 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____7000 args1 =
                            match uu____7000 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____7074 =
                                       let uu____7075 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____7075.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____7074
                                 | (binders3,[]) ->
                                     let uu____7105 =
                                       let uu____7106 =
                                         let uu____7109 =
                                           let uu____7110 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____7110
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____7109
                                          in
                                       uu____7106.FStar_Syntax_Syntax.n  in
                                     (match uu____7105 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____7135 =
                                            let uu____7136 =
                                              let uu____7137 =
                                                let uu____7150 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____7150)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____7137
                                               in
                                            mk1 uu____7136  in
                                          N uu____7135
                                      | uu____7157 -> failwith "wat?")
                                 | ([],uu____7158::uu____7159) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____7199)::binders3,(arg,uu____7202)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____7255 = FStar_List.splitAt n' binders1  in
                          (match uu____7255 with
                           | (binders2,uu____7287) ->
                               let uu____7312 =
                                 let uu____7333 =
                                   FStar_List.map2
                                     (fun uu____7387  ->
                                        fun uu____7388  ->
                                          match (uu____7387, uu____7388) with
                                          | ((bv,uu____7426),(arg,q)) ->
                                              let uu____7443 =
                                                let uu____7444 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____7444.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____7443 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7463 ->
                                                   let uu____7464 =
                                                     let uu____7469 =
                                                       star_type' env arg  in
                                                     (uu____7469, q)  in
                                                   (uu____7464, [(arg, q)])
                                               | uu____7496 ->
                                                   let uu____7497 =
                                                     check_n env arg  in
                                                   (match uu____7497 with
                                                    | (uu____7520,s_arg,u_arg)
                                                        ->
                                                        let uu____7523 =
                                                          let uu____7530 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____7530
                                                          then
                                                            let uu____7537 =
                                                              let uu____7542
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____7542, q)
                                                               in
                                                            [uu____7537;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____7523))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____7333  in
                               (match uu____7312 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____7641 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____7650 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____7641, uu____7650)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7718) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7724) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7730,uu____7731) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7773 = let uu____7774 = env.tc_const c  in N uu____7774
             in
          (uu____7773, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7781 ->
          let uu____7794 =
            let uu____7795 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7795  in
          failwith uu____7794
      | FStar_Syntax_Syntax.Tm_type uu____7802 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7809 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7828 ->
          let uu____7835 =
            let uu____7836 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7836  in
          failwith uu____7835
      | FStar_Syntax_Syntax.Tm_uvar uu____7843 ->
          let uu____7860 =
            let uu____7861 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7861  in
          failwith uu____7860
      | FStar_Syntax_Syntax.Tm_delayed uu____7868 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7899 =
            let uu____7900 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7900  in
          failwith uu____7899

and mk_match :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,FStar_Syntax_Syntax.term'
                                                                 FStar_Syntax_Syntax.syntax
                                                                 FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (env ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____7947 = check_n env e0  in
          match uu____7947 with
          | (uu____7960,s_e0,u_e0) ->
              let uu____7963 =
                let uu____7992 =
                  FStar_List.map
                    (fun b  ->
                       let uu____8053 = FStar_Syntax_Subst.open_branch b  in
                       match uu____8053 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___93_8095 = env  in
                             let uu____8096 =
                               let uu____8097 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____8097
                                in
                             {
                               env = uu____8096;
                               subst = (uu___93_8095.subst);
                               tc_const = (uu___93_8095.tc_const)
                             }  in
                           let uu____8100 = f env1 body  in
                           (match uu____8100 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8172 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____7992  in
              (match uu____7963 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____8274 = FStar_List.hd nms  in
                     match uu____8274 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___76_8280  ->
                          match uu___76_8280 with
                          | M uu____8281 -> true
                          | uu____8282 -> false) nms
                      in
                   let uu____8283 =
                     let uu____8320 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8410  ->
                              match uu____8410 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8587 =
                                         check env original_body (M t2)  in
                                       (match uu____8587 with
                                        | (uu____8624,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8663,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____8320  in
                   (match uu____8283 with
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
                              (fun uu____8847  ->
                                 match uu____8847 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8898 =
                                         let uu____8899 =
                                           let uu____8914 =
                                             let uu____8921 =
                                               let uu____8926 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____8927 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____8926, uu____8927)  in
                                             [uu____8921]  in
                                           (s_body, uu____8914)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8899
                                          in
                                       mk1 uu____8898  in
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
                            let uu____8959 =
                              let uu____8960 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____8960]  in
                            let uu____8961 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____8959 uu____8961
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____8967 =
                              let uu____8974 =
                                let uu____8975 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8975
                                 in
                              [uu____8974]  in
                            let uu____8976 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____8967 uu____8976  in
                          let uu____8979 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____9018 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____8979, uu____9018)
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
                           let uu____9035 =
                             let uu____9038 =
                               let uu____9039 =
                                 let uu____9066 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____9066,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____9039  in
                             mk1 uu____9038  in
                           let uu____9103 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____9035, uu____9103))))

and mk_let :
  env_ ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.term ->
        (env_ ->
           FStar_Syntax_Syntax.term ->
             (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
               FStar_Pervasives_Native.tuple3)
          ->
          (env_ ->
             FStar_Syntax_Syntax.term ->
               (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
                 FStar_Pervasives_Native.tuple3)
            ->
            (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
              FStar_Pervasives_Native.tuple3
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
              let uu____9152 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____9152]  in
            let uu____9153 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____9153 with
            | (x_binders1,e21) ->
                let uu____9166 = infer env e1  in
                (match uu____9166 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____9183 = is_C t1  in
                       if uu____9183
                       then
                         let uu___94_9184 = binding  in
                         let uu____9185 =
                           let uu____9188 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____9188  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___94_9184.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_9184.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9185;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_9184.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___94_9184.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___94_9184.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___94_9184.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___95_9191 = env  in
                       let uu____9192 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___96_9194 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___96_9194.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___96_9194.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9192;
                         subst = (uu___95_9191.subst);
                         tc_const = (uu___95_9191.tc_const)
                       }  in
                     let uu____9195 = proceed env1 e21  in
                     (match uu____9195 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___97_9212 = binding  in
                            let uu____9213 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___97_9212.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___97_9212.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9213;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___97_9212.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___97_9212.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___97_9212.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___97_9212.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____9216 =
                            let uu____9219 =
                              let uu____9220 =
                                let uu____9233 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___98_9243 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___98_9243.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___98_9243.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___98_9243.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___98_9243.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___98_9243.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___98_9243.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9233)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9220  in
                            mk1 uu____9219  in
                          let uu____9244 =
                            let uu____9247 =
                              let uu____9248 =
                                let uu____9261 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___99_9271 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___99_9271.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___99_9271.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___99_9271.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___99_9271.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___99_9271.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___99_9271.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9261)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9248  in
                            mk1 uu____9247  in
                          (nm_rec, uu____9216, uu____9244))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___100_9280 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___100_9280.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___100_9280.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___100_9280.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___100_9280.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___100_9280.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___101_9282 = env  in
                       let uu____9283 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___102_9285 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___102_9285.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___102_9285.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9283;
                         subst = (uu___101_9282.subst);
                         tc_const = (uu___101_9282.tc_const)
                       }  in
                     let uu____9286 = ensure_m env1 e21  in
                     (match uu____9286 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____9309 =
                              let uu____9310 =
                                let uu____9325 =
                                  let uu____9332 =
                                    let uu____9337 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____9338 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9337, uu____9338)  in
                                  [uu____9332]  in
                                (s_e2, uu____9325)  in
                              FStar_Syntax_Syntax.Tm_app uu____9310  in
                            mk1 uu____9309  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____9357 =
                              let uu____9358 =
                                let uu____9373 =
                                  let uu____9380 =
                                    let uu____9385 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____9385)  in
                                  [uu____9380]  in
                                (s_e1, uu____9373)  in
                              FStar_Syntax_Syntax.Tm_app uu____9358  in
                            mk1 uu____9357  in
                          let uu____9400 =
                            let uu____9401 =
                              let uu____9402 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____9402]  in
                            FStar_Syntax_Util.abs uu____9401 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____9403 =
                            let uu____9406 =
                              let uu____9407 =
                                let uu____9420 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___103_9430 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___103_9430.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___103_9430.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___103_9430.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___103_9430.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___103_9430.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___103_9430.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9420)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9407  in
                            mk1 uu____9406  in
                          ((M t2), uu____9400, uu____9403)))

and check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9442 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____9442  in
      let uu____9443 = check env e mn  in
      match uu____9443 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9459 -> failwith "[check_n]: impossible"

and check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9481 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____9481  in
      let uu____9482 = check env e mn  in
      match uu____9482 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9498 -> failwith "[check_m]: impossible"

and comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp =
  fun nm  ->
    match nm with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t

and mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp =
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

and type_of_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  = fun t  -> FStar_Syntax_Util.comp_result t

and trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        (let uu____9528 =
           let uu____9529 = is_C c  in Prims.op_Negation uu____9529  in
         if uu____9528 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____9539 =
           let uu____9540 = FStar_Syntax_Subst.compress c  in
           uu____9540.FStar_Syntax_Syntax.n  in
         match uu____9539 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9565 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____9565 with
              | (wp_head,wp_args) ->
                  ((let uu____9603 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9617 =
                           let uu____9618 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9618
                            in
                         Prims.op_Negation uu____9617)
                       in
                    if uu____9603 then failwith "mismatch" else ());
                   (let uu____9626 =
                      let uu____9627 =
                        let uu____9642 =
                          FStar_List.map2
                            (fun uu____9670  ->
                               fun uu____9671  ->
                                 match (uu____9670, uu____9671) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9710 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____9710
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____9713 =
                                           let uu____9718 =
                                             let uu____9719 =
                                               print_implicit q  in
                                             let uu____9720 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu____9719 uu____9720
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____9718)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____9713)
                                      else ();
                                      (let uu____9722 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____9722, q)))) args wp_args
                           in
                        (head1, uu____9642)  in
                      FStar_Syntax_Syntax.Tm_app uu____9627  in
                    mk1 uu____9626)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____9756 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____9756 with
              | (binders_orig,comp1) ->
                  let uu____9763 =
                    let uu____9778 =
                      FStar_List.map
                        (fun uu____9812  ->
                           match uu____9812 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____9832 = is_C h  in
                               if uu____9832
                               then
                                 let w' =
                                   let uu____9844 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9844
                                    in
                                 let uu____9845 =
                                   let uu____9852 =
                                     let uu____9859 =
                                       let uu____9864 =
                                         let uu____9865 =
                                           let uu____9866 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____9866  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9865
                                          in
                                       (uu____9864, q)  in
                                     [uu____9859]  in
                                   (w', q) :: uu____9852  in
                                 (w', uu____9845)
                               else
                                 (let x =
                                    let uu____9887 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9887
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____9778  in
                  (match uu____9763 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____9942 =
                           let uu____9945 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9945
                            in
                         FStar_Syntax_Subst.subst_comp uu____9942 comp1  in
                       let app =
                         let uu____9949 =
                           let uu____9950 =
                             let uu____9965 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9980 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____9981 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9980, uu____9981)) bvs
                                in
                             (wp, uu____9965)  in
                           FStar_Syntax_Syntax.Tm_app uu____9950  in
                         mk1 uu____9949  in
                       let comp3 =
                         let uu____9989 = type_of_comp comp2  in
                         let uu____9990 = is_monadic_comp comp2  in
                         trans_G env uu____9989 uu____9990 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9992,uu____9993) ->
             trans_F_ env e wp
         | uu____10034 -> failwith "impossible trans_F_")

and trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp
  =
  fun env  ->
    fun h  ->
      fun is_monadic1  ->
        fun wp  ->
          if is_monadic1
          then
            let uu____10039 =
              let uu____10040 = star_type' env h  in
              let uu____10043 =
                let uu____10052 =
                  let uu____10057 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____10057)  in
                [uu____10052]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____10040;
                FStar_Syntax_Syntax.effect_args = uu____10043;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____10039
          else
            (let uu____10067 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____10067)

let n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
  
let star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun t  -> let uu____10086 = n env.env t  in star_type' env uu____10086
  
let star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____10105 = n env.env t  in check_n env uu____10105
  
let trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____10121 = n env.env c  in
        let uu____10122 = n env.env wp  in
        trans_F_ env uu____10121 uu____10122
  