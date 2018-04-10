open Prims
type env =
  {
  env: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }[@@deriving show]
let (__proj__Mkenv__item__env : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__env
  
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__subst
  
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee  ->
    match projectee with
    | { env = __fname__env; subst = __fname__subst;
        tc_const = __fname__tc_const;_} -> __fname__tc_const
  
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env  -> fun tc_const  -> { env; subst = []; tc_const } 
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts,FStar_Syntax_Syntax.eff_decl)
              FStar_Pervasives_Native.tuple2)
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
              let uu___77_119 = a  in
              let uu____120 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___77_119.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___77_119.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____120
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            let uu____128 =
              let uu____129 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____129
              then
                let uu____130 = d "Elaborating extra WP combinators"  in
                let uu____131 = FStar_Syntax_Print.term_to_string wp_a1  in
                FStar_Util.print1 "wp_a is: %s\n" uu____131
              else ()  in
            let rec collect_binders t =
              let uu____144 =
                let uu____145 =
                  let uu____148 = FStar_Syntax_Subst.compress t  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____148
                   in
                uu____145.FStar_Syntax_Syntax.n  in
              match uu____144 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                  let rest =
                    match comp.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Total (t1,uu____179) -> t1
                    | uu____188 -> failwith "wp_a contains non-Tot arrow"  in
                  let uu____191 = collect_binders rest  in
                  FStar_List.append bs uu____191
              | FStar_Syntax_Syntax.Tm_type uu____202 -> []
              | uu____207 -> failwith "wp_a doesn't end in Type0"  in
            let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
            let gamma =
              let uu____226 = collect_binders wp_a1  in
              FStar_All.pipe_right uu____226 FStar_Syntax_Util.name_binders
               in
            let uu____245 =
              let uu____246 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____246
              then
                let uu____247 =
                  let uu____248 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____248  in
                d uu____247
              else ()  in
            let unknown = FStar_Syntax_Syntax.tun  in
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                FStar_Range.dummyRange
               in
            let sigelts = FStar_Util.mk_ref []  in
            let register env1 lident def =
              let uu____278 =
                FStar_TypeChecker_Util.mk_toplevel_definition env1 lident def
                 in
              match uu____278 with
              | (sigelt,fv) ->
                  let uu____285 =
                    let uu____286 =
                      let uu____289 = FStar_ST.op_Bang sigelts  in sigelt ::
                        uu____289
                       in
                    FStar_ST.op_Colon_Equals sigelts uu____286  in
                  fv
               in
            let binders_of_list1 =
              FStar_List.map
                (fun uu____418  ->
                   match uu____418 with
                   | (t,b) ->
                       let uu____429 = FStar_Syntax_Syntax.as_implicit b  in
                       (t, uu____429))
               in
            let mk_all_implicit =
              FStar_List.map
                (fun t  ->
                   let uu____461 = FStar_Syntax_Syntax.as_implicit true  in
                   ((FStar_Pervasives_Native.fst t), uu____461))
               in
            let args_of_binders1 =
              FStar_List.map
                (fun bv  ->
                   let uu____485 =
                     FStar_Syntax_Syntax.bv_to_name
                       (FStar_Pervasives_Native.fst bv)
                      in
                   FStar_Syntax_Syntax.as_arg uu____485)
               in
            let uu____486 =
              let uu____503 =
                let mk2 f =
                  let t =
                    FStar_Syntax_Syntax.gen_bv "t"
                      FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                     in
                  let body =
                    let uu____526 =
                      let uu____529 = FStar_Syntax_Syntax.bv_to_name t  in
                      f uu____529  in
                    FStar_Syntax_Util.arrow gamma uu____526  in
                  let uu____530 =
                    let uu____531 =
                      let uu____538 = FStar_Syntax_Syntax.mk_binder a1  in
                      let uu____539 =
                        let uu____542 = FStar_Syntax_Syntax.mk_binder t  in
                        [uu____542]  in
                      uu____538 :: uu____539  in
                    FStar_List.append binders uu____531  in
                  FStar_Syntax_Util.abs uu____530 body
                    FStar_Pervasives_Native.None
                   in
                let uu____547 = mk2 FStar_Syntax_Syntax.mk_Total  in
                let uu____548 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                (uu____547, uu____548)  in
              match uu____503 with
              | (ctx_def,gctx_def) ->
                  let ctx_lid = mk_lid "ctx"  in
                  let ctx_fv = register env ctx_lid ctx_def  in
                  let gctx_lid = mk_lid "gctx"  in
                  let gctx_fv = register env gctx_lid gctx_def  in
                  let mk_app1 fv t =
                    let uu____586 =
                      let uu____587 =
                        let uu____602 =
                          let uu____609 =
                            FStar_List.map
                              (fun uu____629  ->
                                 match uu____629 with
                                 | (bv,uu____639) ->
                                     let uu____640 =
                                       FStar_Syntax_Syntax.bv_to_name bv  in
                                     let uu____641 =
                                       FStar_Syntax_Syntax.as_implicit false
                                        in
                                     (uu____640, uu____641)) binders
                             in
                          let uu____642 =
                            let uu____649 =
                              let uu____654 =
                                FStar_Syntax_Syntax.bv_to_name a1  in
                              let uu____655 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____654, uu____655)  in
                            let uu____656 =
                              let uu____663 =
                                let uu____668 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (t, uu____668)  in
                              [uu____663]  in
                            uu____649 :: uu____656  in
                          FStar_List.append uu____609 uu____642  in
                        (fv, uu____602)  in
                      FStar_Syntax_Syntax.Tm_app uu____587  in
                    mk1 uu____586  in
                  (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
               in
            match uu____486 with
            | (env1,mk_ctx,mk_gctx) ->
                let c_pure =
                  let t =
                    FStar_Syntax_Syntax.gen_bv "t"
                      FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                     in
                  let x =
                    let uu____733 = FStar_Syntax_Syntax.bv_to_name t  in
                    FStar_Syntax_Syntax.gen_bv "x"
                      FStar_Pervasives_Native.None uu____733
                     in
                  let ret1 =
                    let uu____737 =
                      let uu____738 =
                        let uu____741 = FStar_Syntax_Syntax.bv_to_name t  in
                        mk_ctx uu____741  in
                      FStar_Syntax_Util.residual_tot uu____738  in
                    FStar_Pervasives_Native.Some uu____737  in
                  let body =
                    let uu____743 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.abs gamma uu____743 ret1  in
                  let uu____744 =
                    let uu____745 = mk_all_implicit binders  in
                    let uu____752 =
                      binders_of_list1 [(a1, true); (t, true); (x, false)]
                       in
                    FStar_List.append uu____745 uu____752  in
                  FStar_Syntax_Util.abs uu____744 body ret1  in
                let c_pure1 =
                  let uu____780 = mk_lid "pure"  in
                  register env1 uu____780 c_pure  in
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
                    let uu____785 =
                      let uu____786 =
                        let uu____787 =
                          let uu____794 =
                            let uu____795 =
                              let uu____796 =
                                FStar_Syntax_Syntax.bv_to_name t1  in
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None uu____796
                               in
                            FStar_Syntax_Syntax.mk_binder uu____795  in
                          [uu____794]  in
                        let uu____797 =
                          let uu____800 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          FStar_Syntax_Syntax.mk_GTotal uu____800  in
                        FStar_Syntax_Util.arrow uu____787 uu____797  in
                      mk_gctx uu____786  in
                    FStar_Syntax_Syntax.gen_bv "l"
                      FStar_Pervasives_Native.None uu____785
                     in
                  let r =
                    let uu____802 =
                      let uu____803 = FStar_Syntax_Syntax.bv_to_name t1  in
                      mk_gctx uu____803  in
                    FStar_Syntax_Syntax.gen_bv "r"
                      FStar_Pervasives_Native.None uu____802
                     in
                  let ret1 =
                    let uu____807 =
                      let uu____808 =
                        let uu____811 = FStar_Syntax_Syntax.bv_to_name t2  in
                        mk_gctx uu____811  in
                      FStar_Syntax_Util.residual_tot uu____808  in
                    FStar_Pervasives_Native.Some uu____807  in
                  let outer_body =
                    let gamma_as_args = args_of_binders1 gamma  in
                    let inner_body =
                      let uu____819 = FStar_Syntax_Syntax.bv_to_name l  in
                      let uu____822 =
                        let uu____831 =
                          let uu____834 =
                            let uu____835 =
                              let uu____836 =
                                FStar_Syntax_Syntax.bv_to_name r  in
                              FStar_Syntax_Util.mk_app uu____836
                                gamma_as_args
                               in
                            FStar_Syntax_Syntax.as_arg uu____835  in
                          [uu____834]  in
                        FStar_List.append gamma_as_args uu____831  in
                      FStar_Syntax_Util.mk_app uu____819 uu____822  in
                    FStar_Syntax_Util.abs gamma inner_body ret1  in
                  let uu____839 =
                    let uu____840 = mk_all_implicit binders  in
                    let uu____847 =
                      binders_of_list1
                        [(a1, true);
                        (t1, true);
                        (t2, true);
                        (l, false);
                        (r, false)]
                       in
                    FStar_List.append uu____840 uu____847  in
                  FStar_Syntax_Util.abs uu____839 outer_body ret1  in
                let c_app1 =
                  let uu____883 = mk_lid "app"  in
                  register env1 uu____883 c_app  in
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
                    let uu____890 =
                      let uu____897 =
                        let uu____898 = FStar_Syntax_Syntax.bv_to_name t1  in
                        FStar_Syntax_Syntax.null_binder uu____898  in
                      [uu____897]  in
                    let uu____899 =
                      let uu____902 = FStar_Syntax_Syntax.bv_to_name t2  in
                      FStar_Syntax_Syntax.mk_GTotal uu____902  in
                    FStar_Syntax_Util.arrow uu____890 uu____899  in
                  let f =
                    FStar_Syntax_Syntax.gen_bv "f"
                      FStar_Pervasives_Native.None t_f
                     in
                  let a11 =
                    let uu____905 =
                      let uu____906 = FStar_Syntax_Syntax.bv_to_name t1  in
                      mk_gctx uu____906  in
                    FStar_Syntax_Syntax.gen_bv "a1"
                      FStar_Pervasives_Native.None uu____905
                     in
                  let ret1 =
                    let uu____910 =
                      let uu____911 =
                        let uu____914 = FStar_Syntax_Syntax.bv_to_name t2  in
                        mk_gctx uu____914  in
                      FStar_Syntax_Util.residual_tot uu____911  in
                    FStar_Pervasives_Native.Some uu____910  in
                  let uu____915 =
                    let uu____916 = mk_all_implicit binders  in
                    let uu____923 =
                      binders_of_list1
                        [(a1, true);
                        (t1, true);
                        (t2, true);
                        (f, false);
                        (a11, false)]
                       in
                    FStar_List.append uu____916 uu____923  in
                  let uu____958 =
                    let uu____959 =
                      let uu____968 =
                        let uu____971 =
                          let uu____974 =
                            let uu____983 =
                              let uu____986 =
                                FStar_Syntax_Syntax.bv_to_name f  in
                              [uu____986]  in
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              uu____983
                             in
                          FStar_Syntax_Util.mk_app c_pure1 uu____974  in
                        let uu____987 =
                          let uu____992 = FStar_Syntax_Syntax.bv_to_name a11
                             in
                          [uu____992]  in
                        uu____971 :: uu____987  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____968  in
                    FStar_Syntax_Util.mk_app c_app1 uu____959  in
                  FStar_Syntax_Util.abs uu____915 uu____958 ret1  in
                let c_lift11 =
                  let uu____996 = mk_lid "lift1"  in
                  register env1 uu____996 c_lift1  in
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
                    let uu____1004 =
                      let uu____1011 =
                        let uu____1012 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        FStar_Syntax_Syntax.null_binder uu____1012  in
                      let uu____1013 =
                        let uu____1016 =
                          let uu____1017 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          FStar_Syntax_Syntax.null_binder uu____1017  in
                        [uu____1016]  in
                      uu____1011 :: uu____1013  in
                    let uu____1018 =
                      let uu____1021 = FStar_Syntax_Syntax.bv_to_name t3  in
                      FStar_Syntax_Syntax.mk_GTotal uu____1021  in
                    FStar_Syntax_Util.arrow uu____1004 uu____1018  in
                  let f =
                    FStar_Syntax_Syntax.gen_bv "f"
                      FStar_Pervasives_Native.None t_f
                     in
                  let a11 =
                    let uu____1024 =
                      let uu____1025 = FStar_Syntax_Syntax.bv_to_name t1  in
                      mk_gctx uu____1025  in
                    FStar_Syntax_Syntax.gen_bv "a1"
                      FStar_Pervasives_Native.None uu____1024
                     in
                  let a2 =
                    let uu____1027 =
                      let uu____1028 = FStar_Syntax_Syntax.bv_to_name t2  in
                      mk_gctx uu____1028  in
                    FStar_Syntax_Syntax.gen_bv "a2"
                      FStar_Pervasives_Native.None uu____1027
                     in
                  let ret1 =
                    let uu____1032 =
                      let uu____1033 =
                        let uu____1036 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        mk_gctx uu____1036  in
                      FStar_Syntax_Util.residual_tot uu____1033  in
                    FStar_Pervasives_Native.Some uu____1032  in
                  let uu____1037 =
                    let uu____1038 = mk_all_implicit binders  in
                    let uu____1045 =
                      binders_of_list1
                        [(a1, true);
                        (t1, true);
                        (t2, true);
                        (t3, true);
                        (f, false);
                        (a11, false);
                        (a2, false)]
                       in
                    FStar_List.append uu____1038 uu____1045  in
                  let uu____1088 =
                    let uu____1089 =
                      let uu____1098 =
                        let uu____1101 =
                          let uu____1104 =
                            let uu____1113 =
                              let uu____1116 =
                                let uu____1119 =
                                  let uu____1128 =
                                    let uu____1131 =
                                      FStar_Syntax_Syntax.bv_to_name f  in
                                    [uu____1131]  in
                                  FStar_List.map FStar_Syntax_Syntax.as_arg
                                    uu____1128
                                   in
                                FStar_Syntax_Util.mk_app c_pure1 uu____1119
                                 in
                              let uu____1132 =
                                let uu____1137 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                [uu____1137]  in
                              uu____1116 :: uu____1132  in
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              uu____1113
                             in
                          FStar_Syntax_Util.mk_app c_app1 uu____1104  in
                        let uu____1140 =
                          let uu____1145 = FStar_Syntax_Syntax.bv_to_name a2
                             in
                          [uu____1145]  in
                        uu____1101 :: uu____1140  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____1098
                       in
                    FStar_Syntax_Util.mk_app c_app1 uu____1089  in
                  FStar_Syntax_Util.abs uu____1037 uu____1088 ret1  in
                let c_lift21 =
                  let uu____1149 = mk_lid "lift2"  in
                  register env1 uu____1149 c_lift2  in
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
                    let uu____1156 =
                      let uu____1163 =
                        let uu____1164 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        FStar_Syntax_Syntax.null_binder uu____1164  in
                      [uu____1163]  in
                    let uu____1165 =
                      let uu____1168 =
                        let uu____1169 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1169  in
                      FStar_Syntax_Syntax.mk_Total uu____1168  in
                    FStar_Syntax_Util.arrow uu____1156 uu____1165  in
                  let f =
                    FStar_Syntax_Syntax.gen_bv "f"
                      FStar_Pervasives_Native.None t_f
                     in
                  let ret1 =
                    let uu____1174 =
                      let uu____1175 =
                        let uu____1178 =
                          let uu____1179 =
                            let uu____1186 =
                              let uu____1187 =
                                FStar_Syntax_Syntax.bv_to_name t1  in
                              FStar_Syntax_Syntax.null_binder uu____1187  in
                            [uu____1186]  in
                          let uu____1188 =
                            let uu____1191 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____1191  in
                          FStar_Syntax_Util.arrow uu____1179 uu____1188  in
                        mk_ctx uu____1178  in
                      FStar_Syntax_Util.residual_tot uu____1175  in
                    FStar_Pervasives_Native.Some uu____1174  in
                  let e1 =
                    let uu____1193 = FStar_Syntax_Syntax.bv_to_name t1  in
                    FStar_Syntax_Syntax.gen_bv "e1"
                      FStar_Pervasives_Native.None uu____1193
                     in
                  let body =
                    let uu____1195 =
                      let uu____1196 =
                        let uu____1203 = FStar_Syntax_Syntax.mk_binder e1  in
                        [uu____1203]  in
                      FStar_List.append gamma uu____1196  in
                    let uu____1208 =
                      let uu____1209 = FStar_Syntax_Syntax.bv_to_name f  in
                      let uu____1212 =
                        let uu____1221 =
                          let uu____1222 = FStar_Syntax_Syntax.bv_to_name e1
                             in
                          FStar_Syntax_Syntax.as_arg uu____1222  in
                        let uu____1223 = args_of_binders1 gamma  in
                        uu____1221 :: uu____1223  in
                      FStar_Syntax_Util.mk_app uu____1209 uu____1212  in
                    FStar_Syntax_Util.abs uu____1195 uu____1208 ret1  in
                  let uu____1226 =
                    let uu____1227 = mk_all_implicit binders  in
                    let uu____1234 =
                      binders_of_list1
                        [(a1, true); (t1, true); (t2, true); (f, false)]
                       in
                    FStar_List.append uu____1227 uu____1234  in
                  FStar_Syntax_Util.abs uu____1226 body ret1  in
                let c_push1 =
                  let uu____1266 = mk_lid "push"  in
                  register env1 uu____1266 c_push  in
                let ret_tot_wp_a =
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_tot wp_a1)
                   in
                let mk_generic_app c =
                  if (FStar_List.length binders) > (Prims.parse_int "0")
                  then
                    let uu____1287 =
                      let uu____1288 =
                        let uu____1303 = args_of_binders1 binders  in
                        (c, uu____1303)  in
                      FStar_Syntax_Syntax.Tm_app uu____1288  in
                    mk1 uu____1287
                  else c  in
                let wp_if_then_else =
                  let result_comp =
                    let uu____1313 =
                      let uu____1314 =
                        let uu____1321 =
                          FStar_Syntax_Syntax.null_binder wp_a1  in
                        let uu____1322 =
                          let uu____1325 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          [uu____1325]  in
                        uu____1321 :: uu____1322  in
                      let uu____1326 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1314 uu____1326  in
                    FStar_Syntax_Syntax.mk_Total uu____1313  in
                  let c =
                    FStar_Syntax_Syntax.gen_bv "c"
                      FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                     in
                  let uu____1330 =
                    let uu____1331 =
                      FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                    FStar_List.append binders uu____1331  in
                  let uu____1342 =
                    let l_ite =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "2"))
                        FStar_Pervasives_Native.None
                       in
                    let uu____1344 =
                      let uu____1347 =
                        let uu____1356 =
                          let uu____1359 =
                            let uu____1362 =
                              let uu____1371 =
                                let uu____1372 =
                                  FStar_Syntax_Syntax.bv_to_name c  in
                                FStar_Syntax_Syntax.as_arg uu____1372  in
                              [uu____1371]  in
                            FStar_Syntax_Util.mk_app l_ite uu____1362  in
                          [uu____1359]  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1356
                         in
                      FStar_Syntax_Util.mk_app c_lift21 uu____1347  in
                    FStar_Syntax_Util.ascribe uu____1344
                      ((FStar_Util.Inr result_comp),
                        FStar_Pervasives_Native.None)
                     in
                  FStar_Syntax_Util.abs uu____1330 uu____1342
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                   in
                let wp_if_then_else1 =
                  let uu____1392 = mk_lid "wp_if_then_else"  in
                  register env1 uu____1392 wp_if_then_else  in
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
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  let body =
                    let uu____1403 =
                      let uu____1412 =
                        let uu____1415 =
                          let uu____1418 =
                            let uu____1427 =
                              let uu____1430 =
                                let uu____1433 =
                                  let uu____1442 =
                                    let uu____1443 =
                                      FStar_Syntax_Syntax.bv_to_name q  in
                                    FStar_Syntax_Syntax.as_arg uu____1443  in
                                  [uu____1442]  in
                                FStar_Syntax_Util.mk_app l_and uu____1433  in
                              [uu____1430]  in
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              uu____1427
                             in
                          FStar_Syntax_Util.mk_app c_pure1 uu____1418  in
                        let uu____1448 =
                          let uu____1453 = FStar_Syntax_Syntax.bv_to_name wp
                             in
                          [uu____1453]  in
                        uu____1415 :: uu____1448  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____1412
                       in
                    FStar_Syntax_Util.mk_app c_app1 uu____1403  in
                  let uu____1456 =
                    let uu____1457 =
                      FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                    FStar_List.append binders uu____1457  in
                  FStar_Syntax_Util.abs uu____1456 body ret_tot_wp_a  in
                let wp_assert1 =
                  let uu____1469 = mk_lid "wp_assert"  in
                  register env1 uu____1469 wp_assert  in
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
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  let body =
                    let uu____1480 =
                      let uu____1489 =
                        let uu____1492 =
                          let uu____1495 =
                            let uu____1504 =
                              let uu____1507 =
                                let uu____1510 =
                                  let uu____1519 =
                                    let uu____1520 =
                                      FStar_Syntax_Syntax.bv_to_name q  in
                                    FStar_Syntax_Syntax.as_arg uu____1520  in
                                  [uu____1519]  in
                                FStar_Syntax_Util.mk_app l_imp uu____1510  in
                              [uu____1507]  in
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              uu____1504
                             in
                          FStar_Syntax_Util.mk_app c_pure1 uu____1495  in
                        let uu____1525 =
                          let uu____1530 = FStar_Syntax_Syntax.bv_to_name wp
                             in
                          [uu____1530]  in
                        uu____1492 :: uu____1525  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____1489
                       in
                    FStar_Syntax_Util.mk_app c_app1 uu____1480  in
                  let uu____1533 =
                    let uu____1534 =
                      FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                    FStar_List.append binders uu____1534  in
                  FStar_Syntax_Util.abs uu____1533 body ret_tot_wp_a  in
                let wp_assume1 =
                  let uu____1546 = mk_lid "wp_assume"  in
                  register env1 uu____1546 wp_assume  in
                let wp_assume2 = mk_generic_app wp_assume1  in
                let wp_close =
                  let b =
                    FStar_Syntax_Syntax.gen_bv "b"
                      FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                     in
                  let t_f =
                    let uu____1555 =
                      let uu____1562 =
                        let uu____1563 = FStar_Syntax_Syntax.bv_to_name b  in
                        FStar_Syntax_Syntax.null_binder uu____1563  in
                      [uu____1562]  in
                    let uu____1564 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                    FStar_Syntax_Util.arrow uu____1555 uu____1564  in
                  let f =
                    FStar_Syntax_Syntax.gen_bv "f"
                      FStar_Pervasives_Native.None t_f
                     in
                  let body =
                    let uu____1571 =
                      let uu____1580 =
                        let uu____1583 =
                          let uu____1586 =
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              [FStar_Syntax_Util.tforall]
                             in
                          FStar_Syntax_Util.mk_app c_pure1 uu____1586  in
                        let uu____1595 =
                          let uu____1600 =
                            let uu____1603 =
                              let uu____1612 =
                                let uu____1615 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1615]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1612
                               in
                            FStar_Syntax_Util.mk_app c_push1 uu____1603  in
                          [uu____1600]  in
                        uu____1583 :: uu____1595  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____1580
                       in
                    FStar_Syntax_Util.mk_app c_app1 uu____1571  in
                  let uu____1622 =
                    let uu____1623 =
                      FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                    FStar_List.append binders uu____1623  in
                  FStar_Syntax_Util.abs uu____1622 body ret_tot_wp_a  in
                let wp_close1 =
                  let uu____1635 = mk_lid "wp_close"  in
                  register env1 uu____1635 wp_close  in
                let wp_close2 = mk_generic_app wp_close1  in
                let ret_tot_type =
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                   in
                let ret_gtot_type =
                  let uu____1645 =
                    let uu____1646 =
                      let uu____1647 =
                        FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype
                         in
                      FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                        uu____1647
                       in
                    FStar_Syntax_Util.residual_comp_of_lcomp uu____1646  in
                  FStar_Pervasives_Native.Some uu____1645  in
                let mk_forall1 x body =
                  let uu____1661 =
                    let uu____1666 =
                      let uu____1667 =
                        let uu____1682 =
                          let uu____1685 =
                            let uu____1686 =
                              let uu____1687 =
                                let uu____1688 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____1688]  in
                              FStar_Syntax_Util.abs uu____1687 body
                                ret_tot_type
                               in
                            FStar_Syntax_Syntax.as_arg uu____1686  in
                          [uu____1685]  in
                        (FStar_Syntax_Util.tforall, uu____1682)  in
                      FStar_Syntax_Syntax.Tm_app uu____1667  in
                    FStar_Syntax_Syntax.mk uu____1666  in
                  uu____1661 FStar_Pervasives_Native.None
                    FStar_Range.dummyRange
                   in
                let rec is_discrete t =
                  let uu____1699 =
                    let uu____1700 = FStar_Syntax_Subst.compress t  in
                    uu____1700.FStar_Syntax_Syntax.n  in
                  match uu____1699 with
                  | FStar_Syntax_Syntax.Tm_type uu____1703 -> false
                  | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                      (FStar_List.for_all
                         (fun uu____1729  ->
                            match uu____1729 with
                            | (b,uu____1735) ->
                                is_discrete b.FStar_Syntax_Syntax.sort) bs)
                        && (is_discrete (FStar_Syntax_Util.comp_result c))
                  | uu____1736 -> true  in
                let rec is_monotonic t =
                  let uu____1742 =
                    let uu____1743 = FStar_Syntax_Subst.compress t  in
                    uu____1743.FStar_Syntax_Syntax.n  in
                  match uu____1742 with
                  | FStar_Syntax_Syntax.Tm_type uu____1746 -> true
                  | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                      (FStar_List.for_all
                         (fun uu____1772  ->
                            match uu____1772 with
                            | (b,uu____1778) ->
                                is_discrete b.FStar_Syntax_Syntax.sort) bs)
                        && (is_monotonic (FStar_Syntax_Util.comp_result c))
                  | uu____1779 -> is_discrete t  in
                let rec mk_rel rel t x y =
                  let mk_rel1 = mk_rel rel  in
                  let t1 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta;
                      FStar_TypeChecker_Normalize.Eager_unfolding;
                      FStar_TypeChecker_Normalize.UnfoldUntil
                        FStar_Syntax_Syntax.Delta_constant] env1 t
                     in
                  let uu____1838 =
                    let uu____1839 = FStar_Syntax_Subst.compress t1  in
                    uu____1839.FStar_Syntax_Syntax.n  in
                  match uu____1838 with
                  | FStar_Syntax_Syntax.Tm_type uu____1842 -> rel x y
                  | FStar_Syntax_Syntax.Tm_arrow
                      (binder::[],{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.GTotal
                                      (b,uu____1845);
                                    FStar_Syntax_Syntax.pos = uu____1846;
                                    FStar_Syntax_Syntax.vars = uu____1847;_})
                      ->
                      let a2 =
                        (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                         in
                      let uu____1881 = (is_monotonic a2) || (is_monotonic b)
                         in
                      if uu____1881
                      then
                        let a11 =
                          FStar_Syntax_Syntax.gen_bv "a1"
                            FStar_Pervasives_Native.None a2
                           in
                        let body =
                          let uu____1884 =
                            let uu____1887 =
                              let uu____1896 =
                                let uu____1897 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                FStar_Syntax_Syntax.as_arg uu____1897  in
                              [uu____1896]  in
                            FStar_Syntax_Util.mk_app x uu____1887  in
                          let uu____1898 =
                            let uu____1901 =
                              let uu____1910 =
                                let uu____1911 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                FStar_Syntax_Syntax.as_arg uu____1911  in
                              [uu____1910]  in
                            FStar_Syntax_Util.mk_app y uu____1901  in
                          mk_rel1 b uu____1884 uu____1898  in
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
                           let uu____1916 =
                             let uu____1917 =
                               FStar_Syntax_Syntax.bv_to_name a11  in
                             let uu____1920 =
                               FStar_Syntax_Syntax.bv_to_name a21  in
                             mk_rel1 a2 uu____1917 uu____1920  in
                           let uu____1923 =
                             let uu____1924 =
                               let uu____1927 =
                                 let uu____1936 =
                                   let uu____1937 =
                                     FStar_Syntax_Syntax.bv_to_name a11  in
                                   FStar_Syntax_Syntax.as_arg uu____1937  in
                                 [uu____1936]  in
                               FStar_Syntax_Util.mk_app x uu____1927  in
                             let uu____1938 =
                               let uu____1941 =
                                 let uu____1950 =
                                   let uu____1951 =
                                     FStar_Syntax_Syntax.bv_to_name a21  in
                                   FStar_Syntax_Syntax.as_arg uu____1951  in
                                 [uu____1950]  in
                               FStar_Syntax_Util.mk_app y uu____1941  in
                             mk_rel1 b uu____1924 uu____1938  in
                           FStar_Syntax_Util.mk_imp uu____1916 uu____1923  in
                         let uu____1952 = mk_forall1 a21 body  in
                         mk_forall1 a11 uu____1952)
                  | FStar_Syntax_Syntax.Tm_arrow
                      (binder::[],{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Total
                                      (b,uu____1955);
                                    FStar_Syntax_Syntax.pos = uu____1956;
                                    FStar_Syntax_Syntax.vars = uu____1957;_})
                      ->
                      let a2 =
                        (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                         in
                      let uu____1991 = (is_monotonic a2) || (is_monotonic b)
                         in
                      if uu____1991
                      then
                        let a11 =
                          FStar_Syntax_Syntax.gen_bv "a1"
                            FStar_Pervasives_Native.None a2
                           in
                        let body =
                          let uu____1994 =
                            let uu____1997 =
                              let uu____2006 =
                                let uu____2007 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                FStar_Syntax_Syntax.as_arg uu____2007  in
                              [uu____2006]  in
                            FStar_Syntax_Util.mk_app x uu____1997  in
                          let uu____2008 =
                            let uu____2011 =
                              let uu____2020 =
                                let uu____2021 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                FStar_Syntax_Syntax.as_arg uu____2021  in
                              [uu____2020]  in
                            FStar_Syntax_Util.mk_app y uu____2011  in
                          mk_rel1 b uu____1994 uu____2008  in
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
                           let uu____2026 =
                             let uu____2027 =
                               FStar_Syntax_Syntax.bv_to_name a11  in
                             let uu____2030 =
                               FStar_Syntax_Syntax.bv_to_name a21  in
                             mk_rel1 a2 uu____2027 uu____2030  in
                           let uu____2033 =
                             let uu____2034 =
                               let uu____2037 =
                                 let uu____2046 =
                                   let uu____2047 =
                                     FStar_Syntax_Syntax.bv_to_name a11  in
                                   FStar_Syntax_Syntax.as_arg uu____2047  in
                                 [uu____2046]  in
                               FStar_Syntax_Util.mk_app x uu____2037  in
                             let uu____2048 =
                               let uu____2051 =
                                 let uu____2060 =
                                   let uu____2061 =
                                     FStar_Syntax_Syntax.bv_to_name a21  in
                                   FStar_Syntax_Syntax.as_arg uu____2061  in
                                 [uu____2060]  in
                               FStar_Syntax_Util.mk_app y uu____2051  in
                             mk_rel1 b uu____2034 uu____2048  in
                           FStar_Syntax_Util.mk_imp uu____2026 uu____2033  in
                         let uu____2062 = mk_forall1 a21 body  in
                         mk_forall1 a11 uu____2062)
                  | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                      let t2 =
                        let uu___78_2093 = t1  in
                        let uu____2094 =
                          let uu____2095 =
                            let uu____2108 =
                              let uu____2109 =
                                FStar_Syntax_Util.arrow binders1 comp  in
                              FStar_Syntax_Syntax.mk_Total uu____2109  in
                            ([binder], uu____2108)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____2095  in
                        {
                          FStar_Syntax_Syntax.n = uu____2094;
                          FStar_Syntax_Syntax.pos =
                            (uu___78_2093.FStar_Syntax_Syntax.pos);
                          FStar_Syntax_Syntax.vars =
                            (uu___78_2093.FStar_Syntax_Syntax.vars)
                        }  in
                      mk_rel1 t2 x y
                  | FStar_Syntax_Syntax.Tm_arrow uu____2124 ->
                      failwith "unhandled arrow"
                  | uu____2137 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                    let uu____2155 =
                      let uu____2156 = FStar_Syntax_Subst.compress t1  in
                      uu____2156.FStar_Syntax_Syntax.n  in
                    match uu____2155 with
                    | FStar_Syntax_Syntax.Tm_type uu____2159 ->
                        FStar_Syntax_Util.mk_imp x y
                    | FStar_Syntax_Syntax.Tm_app (head1,args) when
                        let uu____2182 = FStar_Syntax_Subst.compress head1
                           in
                        FStar_Syntax_Util.is_tuple_constructor uu____2182 ->
                        let project i tuple =
                          let projector =
                            let uu____2199 =
                              let uu____2200 =
                                FStar_Parser_Const.mk_tuple_data_lid
                                  (FStar_List.length args)
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.lookup_projector env1
                                uu____2200 i
                               in
                            FStar_Syntax_Syntax.fvar uu____2199
                              (FStar_Syntax_Syntax.Delta_defined_at_level
                                 (Prims.parse_int "1"))
                              FStar_Pervasives_Native.None
                             in
                          FStar_Syntax_Util.mk_app projector
                            [(tuple, FStar_Pervasives_Native.None)]
                           in
                        let uu____2227 =
                          let uu____2234 =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2248  ->
                                   match uu____2248 with
                                   | (t2,q) ->
                                       let uu____2255 = project i x  in
                                       let uu____2256 = project i y  in
                                       mk_stronger t2 uu____2255 uu____2256)
                              args
                             in
                          match uu____2234 with
                          | [] ->
                              failwith
                                "Impossible : Empty application when creating stronger relation in DM4F"
                          | rel0::rels -> (rel0, rels)  in
                        (match uu____2227 with
                         | (rel0,rels) ->
                             FStar_List.fold_left FStar_Syntax_Util.mk_conj
                               rel0 rels)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binders1,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.GTotal
                                      (b,uu____2283);
                                    FStar_Syntax_Syntax.pos = uu____2284;
                                    FStar_Syntax_Syntax.vars = uu____2285;_})
                        ->
                        let bvs =
                          FStar_List.mapi
                            (fun i  ->
                               fun uu____2323  ->
                                 match uu____2323 with
                                 | (bv,q) ->
                                     let uu____2330 =
                                       let uu____2331 =
                                         FStar_Util.string_of_int i  in
                                       Prims.strcat "a" uu____2331  in
                                     FStar_Syntax_Syntax.gen_bv uu____2330
                                       FStar_Pervasives_Native.None
                                       bv.FStar_Syntax_Syntax.sort) binders1
                           in
                        let args =
                          FStar_List.map
                            (fun ai  ->
                               let uu____2338 =
                                 FStar_Syntax_Syntax.bv_to_name ai  in
                               FStar_Syntax_Syntax.as_arg uu____2338) bvs
                           in
                        let body =
                          let uu____2340 = FStar_Syntax_Util.mk_app x args
                             in
                          let uu____2341 = FStar_Syntax_Util.mk_app y args
                             in
                          mk_stronger b uu____2340 uu____2341  in
                        FStar_List.fold_right
                          (fun bv  -> fun body1  -> mk_forall1 bv body1) bvs
                          body
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binders1,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Total
                                      (b,uu____2348);
                                    FStar_Syntax_Syntax.pos = uu____2349;
                                    FStar_Syntax_Syntax.vars = uu____2350;_})
                        ->
                        let bvs =
                          FStar_List.mapi
                            (fun i  ->
                               fun uu____2388  ->
                                 match uu____2388 with
                                 | (bv,q) ->
                                     let uu____2395 =
                                       let uu____2396 =
                                         FStar_Util.string_of_int i  in
                                       Prims.strcat "a" uu____2396  in
                                     FStar_Syntax_Syntax.gen_bv uu____2395
                                       FStar_Pervasives_Native.None
                                       bv.FStar_Syntax_Syntax.sort) binders1
                           in
                        let args =
                          FStar_List.map
                            (fun ai  ->
                               let uu____2403 =
                                 FStar_Syntax_Syntax.bv_to_name ai  in
                               FStar_Syntax_Syntax.as_arg uu____2403) bvs
                           in
                        let body =
                          let uu____2405 = FStar_Syntax_Util.mk_app x args
                             in
                          let uu____2406 = FStar_Syntax_Util.mk_app y args
                             in
                          mk_stronger b uu____2405 uu____2406  in
                        FStar_List.fold_right
                          (fun bv  -> fun body1  -> mk_forall1 bv body1) bvs
                          body
                    | uu____2411 -> failwith "Not a DM elaborated type"  in
                  let body =
                    let uu____2413 = FStar_Syntax_Util.unascribe wp_a1  in
                    let uu____2414 = FStar_Syntax_Syntax.bv_to_name wp1  in
                    let uu____2415 = FStar_Syntax_Syntax.bv_to_name wp2  in
                    mk_stronger uu____2413 uu____2414 uu____2415  in
                  let uu____2416 =
                    let uu____2417 =
                      binders_of_list1
                        [(a1, false); (wp1, false); (wp2, false)]
                       in
                    FStar_List.append binders uu____2417  in
                  FStar_Syntax_Util.abs uu____2416 body ret_tot_type  in
                let stronger1 =
                  let uu____2445 = mk_lid "stronger"  in
                  register env1 uu____2445 stronger  in
                let stronger2 = mk_generic_app stronger1  in
                let wp_ite =
                  let wp =
                    FStar_Syntax_Syntax.gen_bv "wp"
                      FStar_Pervasives_Native.None wp_a1
                     in
                  let uu____2451 = FStar_Util.prefix gamma  in
                  match uu____2451 with
                  | (wp_args,post) ->
                      let k =
                        FStar_Syntax_Syntax.gen_bv "k"
                          FStar_Pervasives_Native.None
                          (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                         in
                      let equiv1 =
                        let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                        let eq1 =
                          let uu____2496 =
                            FStar_Syntax_Syntax.bv_to_name
                              (FStar_Pervasives_Native.fst post)
                             in
                          mk_rel FStar_Syntax_Util.mk_iff
                            k.FStar_Syntax_Syntax.sort k_tm uu____2496
                           in
                        let uu____2499 =
                          FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                        match uu____2499 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                            let k_app =
                              let uu____2509 = args_of_binders1 binders1  in
                              FStar_Syntax_Util.mk_app k_tm uu____2509  in
                            let guard_free1 =
                              let uu____2519 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.guard_free
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Syntax_Syntax.fv_to_tm uu____2519  in
                            let pat =
                              let uu____2523 =
                                let uu____2532 =
                                  FStar_Syntax_Syntax.as_arg k_app  in
                                [uu____2532]  in
                              FStar_Syntax_Util.mk_app guard_free1 uu____2523
                               in
                            let pattern_guarded_body =
                              let uu____2536 =
                                let uu____2537 =
                                  let uu____2544 =
                                    let uu____2545 =
                                      let uu____2556 =
                                        let uu____2559 =
                                          FStar_Syntax_Syntax.as_arg pat  in
                                        [uu____2559]  in
                                      [uu____2556]  in
                                    FStar_Syntax_Syntax.Meta_pattern
                                      uu____2545
                                     in
                                  (body, uu____2544)  in
                                FStar_Syntax_Syntax.Tm_meta uu____2537  in
                              mk1 uu____2536  in
                            FStar_Syntax_Util.close_forall_no_univs binders1
                              pattern_guarded_body
                        | uu____2564 ->
                            failwith
                              "Impossible: Expected the equivalence to be a quantified formula"
                         in
                      let body =
                        let uu____2568 =
                          let uu____2569 =
                            let uu____2570 =
                              let uu____2571 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              let uu____2574 =
                                let uu____2583 = args_of_binders1 wp_args  in
                                let uu____2586 =
                                  let uu____2589 =
                                    let uu____2590 =
                                      FStar_Syntax_Syntax.bv_to_name k  in
                                    FStar_Syntax_Syntax.as_arg uu____2590  in
                                  [uu____2589]  in
                                FStar_List.append uu____2583 uu____2586  in
                              FStar_Syntax_Util.mk_app uu____2571 uu____2574
                               in
                            FStar_Syntax_Util.mk_imp equiv1 uu____2570  in
                          FStar_Syntax_Util.mk_forall_no_univ k uu____2569
                           in
                        FStar_Syntax_Util.abs gamma uu____2568 ret_gtot_type
                         in
                      let uu____2591 =
                        let uu____2592 =
                          FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                        FStar_List.append binders uu____2592  in
                      FStar_Syntax_Util.abs uu____2591 body ret_gtot_type
                   in
                let wp_ite1 =
                  let uu____2604 = mk_lid "wp_ite"  in
                  register env1 uu____2604 wp_ite  in
                let wp_ite2 = mk_generic_app wp_ite1  in
                let null_wp =
                  let wp =
                    FStar_Syntax_Syntax.gen_bv "wp"
                      FStar_Pervasives_Native.None wp_a1
                     in
                  let uu____2610 = FStar_Util.prefix gamma  in
                  match uu____2610 with
                  | (wp_args,post) ->
                      let x =
                        FStar_Syntax_Syntax.gen_bv "x"
                          FStar_Pervasives_Native.None
                          FStar_Syntax_Syntax.tun
                         in
                      let body =
                        let uu____2653 =
                          let uu____2654 =
                            FStar_All.pipe_left
                              FStar_Syntax_Syntax.bv_to_name
                              (FStar_Pervasives_Native.fst post)
                             in
                          let uu____2657 =
                            let uu____2666 =
                              let uu____2667 =
                                FStar_Syntax_Syntax.bv_to_name x  in
                              FStar_Syntax_Syntax.as_arg uu____2667  in
                            [uu____2666]  in
                          FStar_Syntax_Util.mk_app uu____2654 uu____2657  in
                        FStar_Syntax_Util.mk_forall_no_univ x uu____2653  in
                      let uu____2668 =
                        let uu____2669 =
                          let uu____2676 =
                            FStar_Syntax_Syntax.binders_of_list [a1]  in
                          FStar_List.append uu____2676 gamma  in
                        FStar_List.append binders uu____2669  in
                      FStar_Syntax_Util.abs uu____2668 body ret_gtot_type
                   in
                let null_wp1 =
                  let uu____2692 = mk_lid "null_wp"  in
                  register env1 uu____2692 null_wp  in
                let null_wp2 = mk_generic_app null_wp1  in
                let wp_trivial =
                  let wp =
                    FStar_Syntax_Syntax.gen_bv "wp"
                      FStar_Pervasives_Native.None wp_a1
                     in
                  let body =
                    let uu____2701 =
                      let uu____2710 =
                        let uu____2713 = FStar_Syntax_Syntax.bv_to_name a1
                           in
                        let uu____2714 =
                          let uu____2717 =
                            let uu____2720 =
                              let uu____2729 =
                                let uu____2730 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                FStar_Syntax_Syntax.as_arg uu____2730  in
                              [uu____2729]  in
                            FStar_Syntax_Util.mk_app null_wp2 uu____2720  in
                          let uu____2731 =
                            let uu____2736 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2736]  in
                          uu____2717 :: uu____2731  in
                        uu____2713 :: uu____2714  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____2710
                       in
                    FStar_Syntax_Util.mk_app stronger2 uu____2701  in
                  let uu____2739 =
                    let uu____2740 =
                      FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                    FStar_List.append binders uu____2740  in
                  FStar_Syntax_Util.abs uu____2739 body ret_tot_type  in
                let wp_trivial1 =
                  let uu____2752 = mk_lid "wp_trivial"  in
                  register env1 uu____2752 wp_trivial  in
                let wp_trivial2 = mk_generic_app wp_trivial1  in
                let uu____2756 =
                  let uu____2757 =
                    FStar_TypeChecker_Env.debug env1
                      (FStar_Options.Other "ED")
                     in
                  if uu____2757 then d "End Dijkstra monads for free" else ()
                   in
                let c = FStar_Syntax_Subst.close binders  in
                let uu____2763 =
                  let uu____2766 = FStar_ST.op_Bang sigelts  in
                  FStar_List.rev uu____2766  in
                let uu____2818 =
                  let uu___79_2819 = ed  in
                  let uu____2820 =
                    let uu____2821 = c wp_if_then_else2  in ([], uu____2821)
                     in
                  let uu____2824 =
                    let uu____2825 = c wp_ite2  in ([], uu____2825)  in
                  let uu____2828 =
                    let uu____2829 = c stronger2  in ([], uu____2829)  in
                  let uu____2832 =
                    let uu____2833 = c wp_close2  in ([], uu____2833)  in
                  let uu____2836 =
                    let uu____2837 = c wp_assert2  in ([], uu____2837)  in
                  let uu____2840 =
                    let uu____2841 = c wp_assume2  in ([], uu____2841)  in
                  let uu____2844 =
                    let uu____2845 = c null_wp2  in ([], uu____2845)  in
                  let uu____2848 =
                    let uu____2849 = c wp_trivial2  in ([], uu____2849)  in
                  {
                    FStar_Syntax_Syntax.cattributes =
                      (uu___79_2819.FStar_Syntax_Syntax.cattributes);
                    FStar_Syntax_Syntax.mname =
                      (uu___79_2819.FStar_Syntax_Syntax.mname);
                    FStar_Syntax_Syntax.univs =
                      (uu___79_2819.FStar_Syntax_Syntax.univs);
                    FStar_Syntax_Syntax.binders =
                      (uu___79_2819.FStar_Syntax_Syntax.binders);
                    FStar_Syntax_Syntax.signature =
                      (uu___79_2819.FStar_Syntax_Syntax.signature);
                    FStar_Syntax_Syntax.ret_wp =
                      (uu___79_2819.FStar_Syntax_Syntax.ret_wp);
                    FStar_Syntax_Syntax.bind_wp =
                      (uu___79_2819.FStar_Syntax_Syntax.bind_wp);
                    FStar_Syntax_Syntax.if_then_else = uu____2820;
                    FStar_Syntax_Syntax.ite_wp = uu____2824;
                    FStar_Syntax_Syntax.stronger = uu____2828;
                    FStar_Syntax_Syntax.close_wp = uu____2832;
                    FStar_Syntax_Syntax.assert_p = uu____2836;
                    FStar_Syntax_Syntax.assume_p = uu____2840;
                    FStar_Syntax_Syntax.null_wp = uu____2844;
                    FStar_Syntax_Syntax.trivial = uu____2848;
                    FStar_Syntax_Syntax.repr =
                      (uu___79_2819.FStar_Syntax_Syntax.repr);
                    FStar_Syntax_Syntax.return_repr =
                      (uu___79_2819.FStar_Syntax_Syntax.return_repr);
                    FStar_Syntax_Syntax.bind_repr =
                      (uu___79_2819.FStar_Syntax_Syntax.bind_repr);
                    FStar_Syntax_Syntax.actions =
                      (uu___79_2819.FStar_Syntax_Syntax.actions);
                    FStar_Syntax_Syntax.eff_attrs =
                      (uu___79_2819.FStar_Syntax_Syntax.eff_attrs)
                  }  in
                (uu____2763, uu____2818)
  
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___80_2869 = dmff_env  in
      {
        env = env';
        subst = (uu___80_2869.subst);
        tc_const = (uu___80_2869.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____2884 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____2898 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___66_2910  ->
    match uu___66_2910 with
    | FStar_Syntax_Syntax.Total (t,uu____2912) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___65_2925  ->
                match uu___65_2925 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2926 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2928 =
          let uu____2929 =
            let uu____2930 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2930
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2929  in
        failwith uu____2928
    | FStar_Syntax_Syntax.GTotal uu____2931 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___67_2944  ->
    match uu___67_2944 with
    | N t ->
        let uu____2946 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2946
    | M t ->
        let uu____2948 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2948
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2954,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2956;
                      FStar_Syntax_Syntax.vars = uu____2957;_})
        -> nm_of_comp n2
    | uu____2974 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____2984 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____2984 with | M uu____2985 -> true | N uu____2986 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2992 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____3005 =
        let uu____3012 =
          let uu____3013 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3013  in
        [uu____3012]  in
      let uu____3014 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3005 uu____3014  in
    let uu____3017 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3017
  
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
        let uu____3062 =
          let uu____3063 =
            let uu____3076 =
              let uu____3083 =
                let uu____3088 =
                  let uu____3089 = star_type' env a  in
                  FStar_Syntax_Syntax.null_bv uu____3089  in
                let uu____3090 = FStar_Syntax_Syntax.as_implicit false  in
                (uu____3088, uu____3090)  in
              [uu____3083]  in
            let uu____3099 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
            (uu____3076, uu____3099)  in
          FStar_Syntax_Syntax.Tm_arrow uu____3063  in
        mk1 uu____3062

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3130) ->
          let binders1 =
            FStar_List.map
              (fun uu____3166  ->
                 match uu____3166 with
                 | (bv,aqual) ->
                     let uu____3177 =
                       let uu___81_3178 = bv  in
                       let uu____3179 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___81_3178.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___81_3178.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3179
                       }  in
                     (uu____3177, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3182,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3184);
                             FStar_Syntax_Syntax.pos = uu____3185;
                             FStar_Syntax_Syntax.vars = uu____3186;_})
               ->
               let uu____3211 =
                 let uu____3212 =
                   let uu____3225 =
                     let uu____3226 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3226  in
                   (binders1, uu____3225)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3212  in
               mk1 uu____3211
           | uu____3233 ->
               let uu____3234 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3234 with
                | N hn ->
                    let uu____3236 =
                      let uu____3237 =
                        let uu____3250 =
                          let uu____3251 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3251  in
                        (binders1, uu____3250)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3237  in
                    mk1 uu____3236
                | M a ->
                    let uu____3259 =
                      let uu____3260 =
                        let uu____3273 =
                          let uu____3280 =
                            let uu____3287 =
                              let uu____3292 =
                                let uu____3293 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____3293  in
                              let uu____3294 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____3292, uu____3294)  in
                            [uu____3287]  in
                          FStar_List.append binders1 uu____3280  in
                        let uu____3307 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____3273, uu____3307)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3260  in
                    mk1 uu____3259))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  let uu____3379 = FStar_Util.string_builder_append strb "{"
                     in
                  let uu____3380 =
                    let uu____3381 = f x  in
                    FStar_Util.string_builder_append strb uu____3381  in
                  let uu____3382 =
                    FStar_List.iter
                      (fun x1  ->
                         let uu____3387 =
                           FStar_Util.string_builder_append strb ", "  in
                         let uu____3388 = f x1  in
                         FStar_Util.string_builder_append strb uu____3388) xs
                     in
                  let uu____3389 = FStar_Util.string_builder_append strb "}"
                     in
                  FStar_Util.string_of_string_builder strb
               in
            let uu____3390 =
              let uu____3395 =
                let uu____3396 = FStar_Syntax_Print.term_to_string t2  in
                let uu____3397 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3396 uu____3397
                 in
              (FStar_Errors.Warning_DependencyFound, uu____3395)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3390  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3407 =
              let uu____3408 = FStar_Syntax_Subst.compress ty  in
              uu____3408.FStar_Syntax_Syntax.n  in
            match uu____3407 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3429 =
                  let uu____3430 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____3430  in
                if uu____3429
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3458 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____3458 s  in
                       let uu____3461 =
                         let uu____3462 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____3462  in
                       if uu____3461
                       then
                         let uu____3463 = debug1 ty1 sinter  in
                         FStar_Exn.raise Not_found
                       else ()  in
                     let uu____3465 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____3465 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3487  ->
                                  match uu____3487 with
                                  | (bv,uu____3497) ->
                                      let uu____3498 =
                                        non_dependent_or_raise s
                                          bv.FStar_Syntax_Syntax.sort
                                         in
                                      FStar_Util.set_add bv s)
                             FStar_Syntax_Syntax.no_names binders1
                            in
                         let ct = FStar_Syntax_Util.comp_result c1  in
                         let uu____3502 = non_dependent_or_raise s ct  in
                         let k = n1 - (FStar_List.length binders1)  in
                         if k > (Prims.parse_int "0")
                         then is_non_dependent_arrow ct k
                         else true
                   with | Not_found  -> false)
            | uu____3511 ->
                let uu____3512 =
                  let uu____3513 =
                    let uu____3518 =
                      let uu____3519 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3519
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3518)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3513
                   in
                false
             in
          let rec is_valid_application head2 =
            let uu____3525 =
              let uu____3526 = FStar_Syntax_Subst.compress head2  in
              uu____3526.FStar_Syntax_Syntax.n  in
            match uu____3525 with
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
                  (let uu____3531 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____3531)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3533 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____3533 with
                 | ((uu____3542,ty),uu____3544) ->
                     let uu____3549 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____3549
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1
                          in
                       let uu____3557 =
                         let uu____3558 = FStar_Syntax_Subst.compress res  in
                         uu____3558.FStar_Syntax_Syntax.n  in
                       (match uu____3557 with
                        | FStar_Syntax_Syntax.Tm_app uu____3561 -> true
                        | uu____3576 ->
                            let uu____3577 =
                              let uu____3578 =
                                let uu____3583 =
                                  let uu____3584 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3584
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3583)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3578
                               in
                            false)
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3586 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3587 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3589) ->
                is_valid_application t2
            | uu____3594 -> false  in
          let uu____3595 = is_valid_application head1  in
          if uu____3595
          then
            let uu____3596 =
              let uu____3597 =
                let uu____3612 =
                  FStar_List.map
                    (fun uu____3633  ->
                       match uu____3633 with
                       | (t2,qual) ->
                           let uu____3650 = star_type' env t2  in
                           (uu____3650, qual)) args
                   in
                (head1, uu____3612)  in
              FStar_Syntax_Syntax.Tm_app uu____3597  in
            mk1 uu____3596
          else
            (let uu____3660 =
               let uu____3665 =
                 let uu____3666 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3666
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____3665)  in
             FStar_Errors.raise_err uu____3660)
      | FStar_Syntax_Syntax.Tm_bvar uu____3667 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3668 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3669 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3670 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3694 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____3694 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___84_3702 = env  in
                 let uu____3703 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____3703;
                   subst = (uu___84_3702.subst);
                   tc_const = (uu___84_3702.tc_const)
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
               ((let uu___85_3723 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___85_3723.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___85_3723.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3730 =
            let uu____3731 =
              let uu____3738 = star_type' env t2  in (uu____3738, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____3731  in
          mk1 uu____3730
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3786 =
            let uu____3787 =
              let uu____3814 = star_type' env e  in
              let uu____3815 =
                let uu____3830 =
                  let uu____3837 = star_type' env t2  in
                  FStar_Util.Inl uu____3837  in
                (uu____3830, FStar_Pervasives_Native.None)  in
              (uu____3814, uu____3815, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3787  in
          mk1 uu____3786
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3915 =
            let uu____3916 =
              let uu____3943 = star_type' env e  in
              let uu____3944 =
                let uu____3959 =
                  let uu____3966 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____3966  in
                (uu____3959, FStar_Pervasives_Native.None)  in
              (uu____3943, uu____3944, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3916  in
          mk1 uu____3915
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____3997,(uu____3998,FStar_Pervasives_Native.Some uu____3999),uu____4000)
          ->
          let uu____4049 =
            let uu____4054 =
              let uu____4055 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4055
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4054)  in
          FStar_Errors.raise_err uu____4049
      | FStar_Syntax_Syntax.Tm_refine uu____4056 ->
          let uu____4063 =
            let uu____4068 =
              let uu____4069 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4069
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4068)  in
          FStar_Errors.raise_err uu____4063
      | FStar_Syntax_Syntax.Tm_uinst uu____4070 ->
          let uu____4077 =
            let uu____4082 =
              let uu____4083 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4083
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4082)  in
          FStar_Errors.raise_err uu____4077
      | FStar_Syntax_Syntax.Tm_quoted uu____4084 ->
          let uu____4091 =
            let uu____4096 =
              let uu____4097 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4097
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4096)  in
          FStar_Errors.raise_err uu____4091
      | FStar_Syntax_Syntax.Tm_constant uu____4098 ->
          let uu____4099 =
            let uu____4104 =
              let uu____4105 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4105
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4104)  in
          FStar_Errors.raise_err uu____4099
      | FStar_Syntax_Syntax.Tm_match uu____4106 ->
          let uu____4129 =
            let uu____4134 =
              let uu____4135 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4135
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4134)  in
          FStar_Errors.raise_err uu____4129
      | FStar_Syntax_Syntax.Tm_let uu____4136 ->
          let uu____4149 =
            let uu____4154 =
              let uu____4155 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4155
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4154)  in
          FStar_Errors.raise_err uu____4149
      | FStar_Syntax_Syntax.Tm_uvar uu____4156 ->
          let uu____4173 =
            let uu____4178 =
              let uu____4179 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4179
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4178)  in
          FStar_Errors.raise_err uu____4173
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4180 =
            let uu____4185 =
              let uu____4186 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4186
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4185)  in
          FStar_Errors.raise_err uu____4180
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4188 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____4188
      | FStar_Syntax_Syntax.Tm_delayed uu____4191 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___69_4222  ->
    match uu___69_4222 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___68_4229  ->
                match uu___68_4229 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4230 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____4236 =
      let uu____4237 = FStar_Syntax_Subst.compress t  in
      uu____4237.FStar_Syntax_Syntax.n  in
    match uu____4236 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4263 =
            let uu____4264 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____4264  in
          is_C uu____4263  in
        if r
        then
          let uu____4279 =
            let uu____4280 =
              let uu____4281 =
                FStar_List.for_all
                  (fun uu____4289  ->
                     match uu____4289 with | (h,uu____4295) -> is_C h) args
                 in
              Prims.op_Negation uu____4281  in
            if uu____4280 then failwith "not a C (A * C)" else ()  in
          true
        else
          (let uu____4298 =
             let uu____4299 =
               let uu____4300 =
                 FStar_List.for_all
                   (fun uu____4309  ->
                      match uu____4309 with
                      | (h,uu____4315) ->
                          let uu____4316 = is_C h  in
                          Prims.op_Negation uu____4316) args
                  in
               Prims.op_Negation uu____4300  in
             if uu____4299 then failwith "not a C (C * A)" else ()  in
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4336 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____4336 with
         | M t1 ->
             let uu____4338 =
               let uu____4339 = is_C t1  in
               if uu____4339 then failwith "not a C (C -> C)" else ()  in
             true
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4343) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4349) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4355,uu____4356) -> is_C t1
    | uu____4397 -> false
  
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
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
          let uu____4427 =
            let uu____4428 =
              let uu____4443 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____4444 =
                let uu____4451 =
                  let uu____4456 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____4456)  in
                [uu____4451]  in
              (uu____4443, uu____4444)  in
            FStar_Syntax_Syntax.Tm_app uu____4428  in
          mk1 uu____4427  in
        let uu____4471 =
          let uu____4472 = FStar_Syntax_Syntax.mk_binder p  in [uu____4472]
           in
        FStar_Syntax_Util.abs uu____4471 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___70_4477  ->
    match uu___70_4477 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4478 -> false
  
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm ->
        (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun context_nm  ->
        let return_if uu____4710 =
          match uu____4710 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4739 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4741 =
                       let uu____4742 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____4742  in
                     Prims.op_Negation uu____4741)
                   in
                if uu____4739
                then
                  let uu____4743 =
                    let uu____4748 =
                      let uu____4749 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____4750 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____4751 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4749 uu____4750 uu____4751
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4748)  in
                  FStar_Errors.raise_err uu____4743
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) ->
                   let uu____4761 = check1 t1 t2  in (rec_nm, s_e, u_e)
               | (M t1,M t2) ->
                   let uu____4764 = check1 t1 t2  in (rec_nm, s_e, u_e)
               | (N t1,M t2) ->
                   let uu____4767 = check1 t1 t2  in
                   let uu____4768 = mk_return env t1 s_e  in
                   ((M t1), uu____4768, u_e)
               | (M t1,N t2) ->
                   let uu____4771 =
                     let uu____4776 =
                       let uu____4777 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____4778 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____4779 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4777 uu____4778 uu____4779
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4776)
                      in
                   FStar_Errors.raise_err uu____4771)
           in
        let ensure_m env1 e2 =
          let strip_m uu___71_4823 =
            match uu___71_4823 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4839 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____4859 =
                let uu____4864 =
                  let uu____4865 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4865
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4864)  in
              FStar_Errors.raise_error uu____4859 e2.FStar_Syntax_Syntax.pos
          | M uu____4872 ->
              let uu____4873 = check env1 e2 context_nm  in
              strip_m uu____4873
           in
        let uu____4880 =
          let uu____4881 = FStar_Syntax_Subst.compress e  in
          uu____4881.FStar_Syntax_Syntax.n  in
        match uu____4880 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4890 ->
            let uu____4891 = infer env e  in return_if uu____4891
        | FStar_Syntax_Syntax.Tm_name uu____4898 ->
            let uu____4899 = infer env e  in return_if uu____4899
        | FStar_Syntax_Syntax.Tm_fvar uu____4906 ->
            let uu____4907 = infer env e  in return_if uu____4907
        | FStar_Syntax_Syntax.Tm_abs uu____4914 ->
            let uu____4931 = infer env e  in return_if uu____4931
        | FStar_Syntax_Syntax.Tm_constant uu____4938 ->
            let uu____4939 = infer env e  in return_if uu____4939
        | FStar_Syntax_Syntax.Tm_quoted uu____4946 ->
            let uu____4953 = infer env e  in return_if uu____4953
        | FStar_Syntax_Syntax.Tm_app uu____4960 ->
            let uu____4975 = infer env e  in return_if uu____4975
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____4983 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____4983 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5045) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5051) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5057,uu____5058) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5099 ->
            let uu____5112 =
              let uu____5113 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5113  in
            failwith uu____5112
        | FStar_Syntax_Syntax.Tm_type uu____5120 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5127 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5146 ->
            let uu____5153 =
              let uu____5154 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5154  in
            failwith uu____5153
        | FStar_Syntax_Syntax.Tm_uvar uu____5161 ->
            let uu____5178 =
              let uu____5179 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5179  in
            failwith uu____5178
        | FStar_Syntax_Syntax.Tm_delayed uu____5186 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5217 =
              let uu____5218 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5218  in
            failwith uu____5217

and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
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
      let uu____5244 =
        let uu____5245 = FStar_Syntax_Subst.compress e  in
        uu____5245.FStar_Syntax_Syntax.n  in
      match uu____5244 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5263 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____5263
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5308;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5309;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5315 =
                  let uu___86_5316 = rc  in
                  let uu____5317 =
                    let uu____5322 =
                      let uu____5323 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____5323  in
                    FStar_Pervasives_Native.Some uu____5322  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___86_5316.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5317;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___86_5316.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____5315
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___87_5333 = env  in
            let uu____5334 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____5334;
              subst = (uu___87_5333.subst);
              tc_const = (uu___87_5333.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____5354  ->
                 match uu____5354 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___88_5367 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___88_5367.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___88_5367.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____5368 =
            FStar_List.fold_left
              (fun uu____5397  ->
                 fun uu____5398  ->
                   match (uu____5397, uu____5398) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____5446 = is_C c  in
                       if uu____5446
                       then
                         let xw =
                           let uu____5454 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5454
                            in
                         let x =
                           let uu___89_5456 = bv  in
                           let uu____5457 =
                             let uu____5460 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____5460  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___89_5456.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___89_5456.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5457
                           }  in
                         let env3 =
                           let uu___90_5462 = env2  in
                           let uu____5463 =
                             let uu____5466 =
                               let uu____5467 =
                                 let uu____5474 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____5474)  in
                               FStar_Syntax_Syntax.NT uu____5467  in
                             uu____5466 :: (env2.subst)  in
                           {
                             env = (uu___90_5462.env);
                             subst = uu____5463;
                             tc_const = (uu___90_5462.tc_const)
                           }  in
                         let uu____5475 =
                           let uu____5478 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____5479 =
                             let uu____5482 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____5482 :: acc  in
                           uu____5478 :: uu____5479  in
                         (env3, uu____5475)
                       else
                         (let x =
                            let uu___91_5487 = bv  in
                            let uu____5488 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___91_5487.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___91_5487.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5488
                            }  in
                          let uu____5491 =
                            let uu____5494 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____5494 :: acc  in
                          (env2, uu____5491))) (env1, []) binders1
             in
          (match uu____5368 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____5514 =
                 let check_what =
                   let uu____5534 = is_monadic rc_opt1  in
                   if uu____5534 then check_m else check_n  in
                 let uu____5548 = check_what env2 body1  in
                 match uu____5548 with
                 | (t,s_body,u_body) ->
                     let uu____5564 =
                       let uu____5565 =
                         let uu____5566 = is_monadic rc_opt1  in
                         if uu____5566 then M t else N t  in
                       comp_of_nm uu____5565  in
                     (uu____5564, s_body, u_body)
                  in
               (match uu____5514 with
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
                                 let uu____5591 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___72_5595  ->
                                           match uu___72_5595 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5596 -> false))
                                    in
                                 if uu____5591
                                 then
                                   let uu____5597 =
                                     FStar_List.filter
                                       (fun uu___73_5601  ->
                                          match uu___73_5601 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5602 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5597
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5611 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___74_5615  ->
                                         match uu___74_5615 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5616 -> false))
                                  in
                               if uu____5611
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___75_5623  ->
                                        match uu___75_5623 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5624 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____5625 =
                                   let uu____5626 =
                                     let uu____5631 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____5631
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5626 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____5625
                               else
                                 (let uu____5633 =
                                    let uu___92_5634 = rc  in
                                    let uu____5635 =
                                      let uu____5640 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____5640
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___92_5634.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5635;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___92_5634.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____5633))
                       in
                    let uu____5641 =
                      let comp1 =
                        let uu____5651 = is_monadic rc_opt1  in
                        let uu____5652 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5651 uu____5652
                         in
                      let uu____5653 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____5653,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____5641 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____5695 =
                             let uu____5696 =
                               let uu____5713 =
                                 let uu____5716 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____5716 s_rc_opt  in
                               (s_binders1, s_body1, uu____5713)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5696  in
                           mk1 uu____5695  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____5726 =
                             let uu____5727 =
                               let uu____5744 =
                                 let uu____5747 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____5747 u_rc_opt  in
                               (u_binders2, u_body2, uu____5744)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5727  in
                           mk1 uu____5726  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5757;_};
            FStar_Syntax_Syntax.fv_delta = uu____5758;
            FStar_Syntax_Syntax.fv_qual = uu____5759;_}
          ->
          let uu____5762 =
            let uu____5767 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5767  in
          (match uu____5762 with
           | (uu____5798,t) ->
               let uu____5800 =
                 let uu____5801 = normalize1 t  in N uu____5801  in
               (uu____5800, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5802;
             FStar_Syntax_Syntax.vars = uu____5803;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5866 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5866 with
           | (unary_op,uu____5888) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5947;
             FStar_Syntax_Syntax.vars = uu____5948;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6024 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6024 with
           | (unary_op,uu____6046) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6111;
             FStar_Syntax_Syntax.vars = uu____6112;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____6150 = infer env a  in
          (match uu____6150 with
           | (t,s,u) ->
               let uu____6166 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6166 with
                | (head1,uu____6188) ->
                    let uu____6209 =
                      let uu____6210 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____6210  in
                    let uu____6211 =
                      let uu____6214 =
                        let uu____6215 =
                          let uu____6230 =
                            let uu____6233 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6233]  in
                          (head1, uu____6230)  in
                        FStar_Syntax_Syntax.Tm_app uu____6215  in
                      mk1 uu____6214  in
                    let uu____6238 =
                      let uu____6241 =
                        let uu____6242 =
                          let uu____6257 =
                            let uu____6260 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6260]  in
                          (head1, uu____6257)  in
                        FStar_Syntax_Syntax.Tm_app uu____6242  in
                      mk1 uu____6241  in
                    (uu____6209, uu____6211, uu____6238)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6269;
             FStar_Syntax_Syntax.vars = uu____6270;_},(a1,uu____6272)::a2::[])
          ->
          let uu____6314 = infer env a1  in
          (match uu____6314 with
           | (t,s,u) ->
               let uu____6330 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6330 with
                | (head1,uu____6352) ->
                    let uu____6373 =
                      let uu____6376 =
                        let uu____6377 =
                          let uu____6392 =
                            let uu____6395 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6395; a2]  in
                          (head1, uu____6392)  in
                        FStar_Syntax_Syntax.Tm_app uu____6377  in
                      mk1 uu____6376  in
                    let uu____6412 =
                      let uu____6415 =
                        let uu____6416 =
                          let uu____6431 =
                            let uu____6434 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6434; a2]  in
                          (head1, uu____6431)  in
                        FStar_Syntax_Syntax.Tm_app uu____6416  in
                      mk1 uu____6415  in
                    (t, uu____6373, uu____6412)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6455;
             FStar_Syntax_Syntax.vars = uu____6456;_},uu____6457)
          ->
          let uu____6478 =
            let uu____6483 =
              let uu____6484 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6484
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6483)  in
          FStar_Errors.raise_error uu____6478 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6491;
             FStar_Syntax_Syntax.vars = uu____6492;_},uu____6493)
          ->
          let uu____6514 =
            let uu____6519 =
              let uu____6520 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6520
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6519)  in
          FStar_Errors.raise_error uu____6514 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6549 = check_n env head1  in
          (match uu____6549 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6570 =
                   let uu____6571 = FStar_Syntax_Subst.compress t  in
                   uu____6571.FStar_Syntax_Syntax.n  in
                 match uu____6570 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6574 -> true
                 | uu____6587 -> false  in
               let rec flatten1 t =
                 let uu____6605 =
                   let uu____6606 = FStar_Syntax_Subst.compress t  in
                   uu____6606.FStar_Syntax_Syntax.n  in
                 match uu____6605 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6623);
                                FStar_Syntax_Syntax.pos = uu____6624;
                                FStar_Syntax_Syntax.vars = uu____6625;_})
                     when is_arrow t1 ->
                     let uu____6650 = flatten1 t1  in
                     (match uu____6650 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6732,uu____6733)
                     -> flatten1 e1
                 | uu____6774 ->
                     let uu____6775 =
                       let uu____6780 =
                         let uu____6781 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6781
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6780)  in
                     FStar_Errors.raise_err uu____6775
                  in
               let uu____6794 = flatten1 t_head  in
               (match uu____6794 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    let uu____6843 =
                      if
                        (FStar_List.length binders) <
                          (FStar_List.length args)
                      then
                        let uu____6854 =
                          let uu____6859 =
                            let uu____6860 = FStar_Util.string_of_int n1  in
                            let uu____6867 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____6878 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6860 uu____6867 uu____6878
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6859)
                           in
                        FStar_Errors.raise_err uu____6854
                      else ()  in
                    let uu____6886 =
                      FStar_Syntax_Subst.open_comp binders comp  in
                    (match uu____6886 with
                     | (binders1,comp1) ->
                         let rec final_type subst1 uu____6930 args1 =
                           match uu____6930 with
                           | (binders2,comp2) ->
                               (match (binders2, args1) with
                                | ([],[]) ->
                                    let uu____7004 =
                                      let uu____7005 =
                                        FStar_Syntax_Subst.subst_comp subst1
                                          comp2
                                         in
                                      uu____7005.FStar_Syntax_Syntax.n  in
                                    nm_of_comp uu____7004
                                | (binders3,[]) ->
                                    let uu____7035 =
                                      let uu____7036 =
                                        let uu____7039 =
                                          let uu____7040 =
                                            mk1
                                              (FStar_Syntax_Syntax.Tm_arrow
                                                 (binders3, comp2))
                                             in
                                          FStar_Syntax_Subst.subst subst1
                                            uu____7040
                                           in
                                        FStar_Syntax_Subst.compress
                                          uu____7039
                                         in
                                      uu____7036.FStar_Syntax_Syntax.n  in
                                    (match uu____7035 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (binders4,comp3) ->
                                         let uu____7065 =
                                           let uu____7066 =
                                             let uu____7067 =
                                               let uu____7080 =
                                                 FStar_Syntax_Subst.close_comp
                                                   binders4 comp3
                                                  in
                                               (binders4, uu____7080)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____7067
                                              in
                                           mk1 uu____7066  in
                                         N uu____7065
                                     | uu____7087 -> failwith "wat?")
                                | ([],uu____7088::uu____7089) ->
                                    failwith "just checked that?!"
                                | ((bv,uu____7129)::binders3,(arg,uu____7132)::args2)
                                    ->
                                    final_type
                                      ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                      subst1) (binders3, comp2) args2)
                            in
                         let final_type1 =
                           final_type [] (binders1, comp1) args  in
                         let uu____7185 = FStar_List.splitAt n' binders1  in
                         (match uu____7185 with
                          | (binders2,uu____7217) ->
                              let uu____7242 =
                                let uu____7263 =
                                  FStar_List.map2
                                    (fun uu____7317  ->
                                       fun uu____7318  ->
                                         match (uu____7317, uu____7318) with
                                         | ((bv,uu____7356),(arg,q)) ->
                                             let uu____7373 =
                                               let uu____7374 =
                                                 FStar_Syntax_Subst.compress
                                                   bv.FStar_Syntax_Syntax.sort
                                                  in
                                               uu____7374.FStar_Syntax_Syntax.n
                                                in
                                             (match uu____7373 with
                                              | FStar_Syntax_Syntax.Tm_type
                                                  uu____7393 ->
                                                  let uu____7394 =
                                                    let uu____7399 =
                                                      star_type' env arg  in
                                                    (uu____7399, q)  in
                                                  (uu____7394, [(arg, q)])
                                              | uu____7426 ->
                                                  let uu____7427 =
                                                    check_n env arg  in
                                                  (match uu____7427 with
                                                   | (uu____7450,s_arg,u_arg)
                                                       ->
                                                       let uu____7453 =
                                                         let uu____7460 =
                                                           is_C
                                                             bv.FStar_Syntax_Syntax.sort
                                                            in
                                                         if uu____7460
                                                         then
                                                           let uu____7467 =
                                                             let uu____7472 =
                                                               FStar_Syntax_Subst.subst
                                                                 env.subst
                                                                 s_arg
                                                                in
                                                             (uu____7472, q)
                                                              in
                                                           [uu____7467;
                                                           (u_arg, q)]
                                                         else [(u_arg, q)]
                                                          in
                                                       ((s_arg, q),
                                                         uu____7453))))
                                    binders2 args
                                   in
                                FStar_List.split uu____7263  in
                              (match uu____7242 with
                               | (s_args,u_args) ->
                                   let u_args1 = FStar_List.flatten u_args
                                      in
                                   let uu____7571 =
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_app
                                          (s_head, s_args))
                                      in
                                   let uu____7580 =
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_app
                                          (u_head, u_args1))
                                      in
                                   (final_type1, uu____7571, uu____7580))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7648) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7654) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7660,uu____7661) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7703 = let uu____7704 = env.tc_const c  in N uu____7704
             in
          (uu____7703, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7711 ->
          let uu____7724 =
            let uu____7725 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7725  in
          failwith uu____7724
      | FStar_Syntax_Syntax.Tm_type uu____7732 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7739 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7758 ->
          let uu____7765 =
            let uu____7766 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7766  in
          failwith uu____7765
      | FStar_Syntax_Syntax.Tm_uvar uu____7773 ->
          let uu____7790 =
            let uu____7791 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7791  in
          failwith uu____7790
      | FStar_Syntax_Syntax.Tm_delayed uu____7798 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7829 =
            let uu____7830 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7830  in
          failwith uu____7829

and (mk_match :
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
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e0  ->
      fun branches  ->
        fun f  ->
          let mk1 x =
            FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
              e0.FStar_Syntax_Syntax.pos
             in
          let uu____7876 = check_n env e0  in
          match uu____7876 with
          | (uu____7889,s_e0,u_e0) ->
              let uu____7892 =
                let uu____7921 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7982 = FStar_Syntax_Subst.open_branch b  in
                       match uu____7982 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___93_8024 = env  in
                             let uu____8025 =
                               let uu____8026 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____8026
                                in
                             {
                               env = uu____8025;
                               subst = (uu___93_8024.subst);
                               tc_const = (uu___93_8024.tc_const)
                             }  in
                           let uu____8029 = f env1 body  in
                           (match uu____8029 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8101 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____7921  in
              (match uu____7892 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____8203 = FStar_List.hd nms  in
                     match uu____8203 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___76_8209  ->
                          match uu___76_8209 with
                          | M uu____8210 -> true
                          | uu____8211 -> false) nms
                      in
                   let uu____8212 =
                     let uu____8249 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8339  ->
                              match uu____8339 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8516 =
                                         check env original_body (M t2)  in
                                       (match uu____8516 with
                                        | (uu____8553,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8592,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____8249  in
                   (match uu____8212 with
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
                              (fun uu____8776  ->
                                 match uu____8776 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8827 =
                                         let uu____8828 =
                                           let uu____8843 =
                                             let uu____8850 =
                                               let uu____8855 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____8856 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____8855, uu____8856)  in
                                             [uu____8850]  in
                                           (s_body, uu____8843)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8828
                                          in
                                       mk1 uu____8827  in
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
                            let uu____8888 =
                              let uu____8889 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____8889]  in
                            let uu____8890 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____8888 uu____8890
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____8896 =
                              let uu____8903 =
                                let uu____8904 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8904
                                 in
                              [uu____8903]  in
                            let uu____8905 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____8896 uu____8905  in
                          let uu____8908 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____8947 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____8908, uu____8947)
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
                           let uu____8964 =
                             let uu____8967 =
                               let uu____8968 =
                                 let uu____8995 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____8995,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8968  in
                             mk1 uu____8967  in
                           let uu____9032 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____8964, uu____9032))))

and (mk_let :
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
              FStar_Pervasives_Native.tuple3)
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
              let uu____9080 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____9080]  in
            let uu____9081 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____9081 with
            | (x_binders1,e21) ->
                let uu____9094 = infer env e1  in
                (match uu____9094 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____9111 = is_C t1  in
                       if uu____9111
                       then
                         let uu___94_9112 = binding  in
                         let uu____9113 =
                           let uu____9116 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____9116  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___94_9112.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_9112.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9113;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_9112.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___94_9112.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___94_9112.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___94_9112.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___95_9119 = env  in
                       let uu____9120 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___96_9122 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___96_9122.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___96_9122.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9120;
                         subst = (uu___95_9119.subst);
                         tc_const = (uu___95_9119.tc_const)
                       }  in
                     let uu____9123 = proceed env1 e21  in
                     (match uu____9123 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___97_9140 = binding  in
                            let uu____9141 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___97_9140.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___97_9140.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9141;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___97_9140.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___97_9140.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___97_9140.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___97_9140.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____9144 =
                            let uu____9147 =
                              let uu____9148 =
                                let uu____9161 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___98_9171 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___98_9171.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___98_9171.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___98_9171.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___98_9171.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___98_9171.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___98_9171.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9161)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9148  in
                            mk1 uu____9147  in
                          let uu____9172 =
                            let uu____9175 =
                              let uu____9176 =
                                let uu____9189 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___99_9199 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___99_9199.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___99_9199.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___99_9199.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___99_9199.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___99_9199.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___99_9199.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9189)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9176  in
                            mk1 uu____9175  in
                          (nm_rec, uu____9144, uu____9172))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___100_9208 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___100_9208.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___100_9208.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___100_9208.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___100_9208.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___100_9208.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___101_9210 = env  in
                       let uu____9211 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___102_9213 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___102_9213.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___102_9213.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9211;
                         subst = (uu___101_9210.subst);
                         tc_const = (uu___101_9210.tc_const)
                       }  in
                     let uu____9214 = ensure_m env1 e21  in
                     (match uu____9214 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____9237 =
                              let uu____9238 =
                                let uu____9253 =
                                  let uu____9260 =
                                    let uu____9265 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____9266 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9265, uu____9266)  in
                                  [uu____9260]  in
                                (s_e2, uu____9253)  in
                              FStar_Syntax_Syntax.Tm_app uu____9238  in
                            mk1 uu____9237  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____9285 =
                              let uu____9286 =
                                let uu____9301 =
                                  let uu____9308 =
                                    let uu____9313 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____9313)  in
                                  [uu____9308]  in
                                (s_e1, uu____9301)  in
                              FStar_Syntax_Syntax.Tm_app uu____9286  in
                            mk1 uu____9285  in
                          let uu____9328 =
                            let uu____9329 =
                              let uu____9330 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____9330]  in
                            FStar_Syntax_Util.abs uu____9329 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____9331 =
                            let uu____9334 =
                              let uu____9335 =
                                let uu____9348 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___103_9358 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___103_9358.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___103_9358.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___103_9358.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___103_9358.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___103_9358.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___103_9358.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9348)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9335  in
                            mk1 uu____9334  in
                          ((M t2), uu____9328, uu____9331)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9370 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____9370  in
      let uu____9371 = check env e mn  in
      match uu____9371 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9387 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9409 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____9409  in
      let uu____9410 = check env e mn  in
      match uu____9410 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9426 -> failwith "[check_m]: impossible"

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
        let uu____9455 =
          let uu____9456 =
            let uu____9457 = is_C c  in Prims.op_Negation uu____9457  in
          if uu____9456 then failwith "not a C" else ()  in
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            c.FStar_Syntax_Syntax.pos
           in
        let uu____9466 =
          let uu____9467 = FStar_Syntax_Subst.compress c  in
          uu____9467.FStar_Syntax_Syntax.n  in
        match uu____9466 with
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let uu____9492 = FStar_Syntax_Util.head_and_args wp  in
            (match uu____9492 with
             | (wp_head,wp_args) ->
                 let uu____9529 =
                   let uu____9530 =
                     (Prims.op_Negation
                        ((FStar_List.length wp_args) =
                           (FStar_List.length args)))
                       ||
                       (let uu____9544 =
                          let uu____9545 =
                            FStar_Parser_Const.mk_tuple_data_lid
                              (FStar_List.length wp_args)
                              FStar_Range.dummyRange
                             in
                          FStar_Syntax_Util.is_constructor wp_head uu____9545
                           in
                        Prims.op_Negation uu____9544)
                      in
                   if uu____9530 then failwith "mismatch" else ()  in
                 let uu____9553 =
                   let uu____9554 =
                     let uu____9569 =
                       FStar_List.map2
                         (fun uu____9597  ->
                            fun uu____9598  ->
                              match (uu____9597, uu____9598) with
                              | ((arg,q),(wp_arg,q')) ->
                                  let print_implicit q1 =
                                    let uu____9636 =
                                      FStar_Syntax_Syntax.is_implicit q1  in
                                    if uu____9636
                                    then "implicit"
                                    else "explicit"  in
                                  let uu____9638 =
                                    if q <> q'
                                    then
                                      let uu____9639 =
                                        let uu____9644 =
                                          let uu____9645 = print_implicit q
                                             in
                                          let uu____9646 = print_implicit q'
                                             in
                                          FStar_Util.format2
                                            "Incoherent implicit qualifiers %b %b\n"
                                            uu____9645 uu____9646
                                           in
                                        (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                          uu____9644)
                                         in
                                      FStar_Errors.log_issue
                                        head1.FStar_Syntax_Syntax.pos
                                        uu____9639
                                    else ()  in
                                  let uu____9648 = trans_F_ env arg wp_arg
                                     in
                                  (uu____9648, q)) args wp_args
                        in
                     (head1, uu____9569)  in
                   FStar_Syntax_Syntax.Tm_app uu____9554  in
                 mk1 uu____9553)
        | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
            let binders1 = FStar_Syntax_Util.name_binders binders  in
            let uu____9682 = FStar_Syntax_Subst.open_comp binders1 comp  in
            (match uu____9682 with
             | (binders_orig,comp1) ->
                 let uu____9689 =
                   let uu____9704 =
                     FStar_List.map
                       (fun uu____9738  ->
                          match uu____9738 with
                          | (bv,q) ->
                              let h = bv.FStar_Syntax_Syntax.sort  in
                              let uu____9758 = is_C h  in
                              if uu____9758
                              then
                                let w' =
                                  let uu____9770 = star_type' env h  in
                                  FStar_Syntax_Syntax.gen_bv
                                    (Prims.strcat
                                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                       "__w'") FStar_Pervasives_Native.None
                                    uu____9770
                                   in
                                let uu____9771 =
                                  let uu____9778 =
                                    let uu____9785 =
                                      let uu____9790 =
                                        let uu____9791 =
                                          let uu____9792 =
                                            FStar_Syntax_Syntax.bv_to_name w'
                                             in
                                          trans_F_ env h uu____9792  in
                                        FStar_Syntax_Syntax.null_bv
                                          uu____9791
                                         in
                                      (uu____9790, q)  in
                                    [uu____9785]  in
                                  (w', q) :: uu____9778  in
                                (w', uu____9771)
                              else
                                (let x =
                                   let uu____9813 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__x") FStar_Pervasives_Native.None
                                     uu____9813
                                    in
                                 (x, [(x, q)]))) binders_orig
                      in
                   FStar_List.split uu____9704  in
                 (match uu____9689 with
                  | (bvs,binders2) ->
                      let binders3 = FStar_List.flatten binders2  in
                      let comp2 =
                        let uu____9868 =
                          let uu____9871 =
                            FStar_Syntax_Syntax.binders_of_list bvs  in
                          FStar_Syntax_Util.rename_binders binders_orig
                            uu____9871
                           in
                        FStar_Syntax_Subst.subst_comp uu____9868 comp1  in
                      let app =
                        let uu____9875 =
                          let uu____9876 =
                            let uu____9891 =
                              FStar_List.map
                                (fun bv  ->
                                   let uu____9906 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   let uu____9907 =
                                     FStar_Syntax_Syntax.as_implicit false
                                      in
                                   (uu____9906, uu____9907)) bvs
                               in
                            (wp, uu____9891)  in
                          FStar_Syntax_Syntax.Tm_app uu____9876  in
                        mk1 uu____9875  in
                      let comp3 =
                        let uu____9915 = type_of_comp comp2  in
                        let uu____9916 = is_monadic_comp comp2  in
                        trans_G env uu____9915 uu____9916 app  in
                      FStar_Syntax_Util.arrow binders3 comp3))
        | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9918,uu____9919) ->
            trans_F_ env e wp
        | uu____9960 -> failwith "impossible trans_F_"

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
            let uu____9965 =
              let uu____9966 = star_type' env h  in
              let uu____9969 =
                let uu____9978 =
                  let uu____9983 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____9983)  in
                [uu____9978]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9966;
                FStar_Syntax_Syntax.effect_args = uu____9969;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____9965
          else
            (let uu____9993 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____9993)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____10012 = n env.env t  in star_type' env uu____10012
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____10031 = n env.env t  in check_n env uu____10031
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____10047 = n env.env c  in
        let uu____10048 = n env.env wp  in
        trans_F_ env uu____10047 uu____10048
  