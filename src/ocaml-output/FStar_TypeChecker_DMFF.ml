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
            let uu____129 =
              let uu____130 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____130
              then
                let uu____131 = d "Elaborating extra WP combinators"  in
                let uu____132 = FStar_Syntax_Print.term_to_string wp_a1  in
                FStar_Util.print1 "wp_a is: %s\n" uu____132
              else ()  in
            let rec collect_binders t =
              let uu____146 =
                let uu____147 =
                  let uu____150 = FStar_Syntax_Subst.compress t  in
                  FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____150
                   in
                uu____147.FStar_Syntax_Syntax.n  in
              match uu____146 with
              | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                  let rest =
                    match comp.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Total (t1,uu____181) -> t1
                    | uu____190 -> failwith "wp_a contains non-Tot arrow"  in
                  let uu____193 = collect_binders rest  in
                  FStar_List.append bs uu____193
              | FStar_Syntax_Syntax.Tm_type uu____204 -> []
              | uu____209 -> failwith "wp_a doesn't end in Type0"  in
            let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
            let gamma =
              let uu____229 = collect_binders wp_a1  in
              FStar_All.pipe_right uu____229 FStar_Syntax_Util.name_binders
               in
            let uu____248 =
              let uu____249 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____249
              then
                let uu____250 =
                  let uu____251 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____251  in
                d uu____250
              else ()  in
            let unknown = FStar_Syntax_Syntax.tun  in
            let mk1 x =
              FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                FStar_Range.dummyRange
               in
            let sigelts = FStar_Util.mk_ref []  in
            let register env1 lident def =
              let uu____285 =
                FStar_TypeChecker_Util.mk_toplevel_definition env1 lident def
                 in
              match uu____285 with
              | (sigelt,fv) ->
                  let uu____292 =
                    let uu____293 =
                      let uu____296 = FStar_ST.op_Bang sigelts  in sigelt ::
                        uu____296
                       in
                    FStar_ST.op_Colon_Equals sigelts uu____293  in
                  fv
               in
            let binders_of_list1 =
              FStar_List.map
                (fun uu____426  ->
                   match uu____426 with
                   | (t,b) ->
                       let uu____437 = FStar_Syntax_Syntax.as_implicit b  in
                       (t, uu____437))
               in
            let mk_all_implicit =
              FStar_List.map
                (fun t  ->
                   let uu____470 = FStar_Syntax_Syntax.as_implicit true  in
                   ((FStar_Pervasives_Native.fst t), uu____470))
               in
            let args_of_binders1 =
              FStar_List.map
                (fun bv  ->
                   let uu____495 =
                     FStar_Syntax_Syntax.bv_to_name
                       (FStar_Pervasives_Native.fst bv)
                      in
                   FStar_Syntax_Syntax.as_arg uu____495)
               in
            let uu____496 =
              let uu____513 =
                let mk2 f =
                  let t =
                    FStar_Syntax_Syntax.gen_bv "t"
                      FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                     in
                  let body =
                    let uu____537 = f (FStar_Syntax_Syntax.bv_to_name t)  in
                    FStar_Syntax_Util.arrow gamma uu____537  in
                  let uu____540 =
                    let uu____541 =
                      let uu____548 = FStar_Syntax_Syntax.mk_binder a1  in
                      let uu____549 =
                        let uu____552 = FStar_Syntax_Syntax.mk_binder t  in
                        [uu____552]  in
                      uu____548 :: uu____549  in
                    FStar_List.append binders uu____541  in
                  FStar_Syntax_Util.abs uu____540 body
                    FStar_Pervasives_Native.None
                   in
                let uu____557 = mk2 FStar_Syntax_Syntax.mk_Total  in
                let uu____558 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                (uu____557, uu____558)  in
              match uu____513 with
              | (ctx_def,gctx_def) ->
                  let ctx_lid = mk_lid "ctx"  in
                  let ctx_fv = register env ctx_lid ctx_def  in
                  let gctx_lid = mk_lid "gctx"  in
                  let gctx_fv = register env gctx_lid gctx_def  in
                  let mk_app1 fv t =
                    let uu____598 =
                      let uu____599 =
                        let uu____614 =
                          let uu____621 =
                            FStar_List.map
                              (fun uu____641  ->
                                 match uu____641 with
                                 | (bv,uu____651) ->
                                     let uu____652 =
                                       FStar_Syntax_Syntax.bv_to_name bv  in
                                     let uu____653 =
                                       FStar_Syntax_Syntax.as_implicit false
                                        in
                                     (uu____652, uu____653)) binders
                             in
                          let uu____654 =
                            let uu____661 =
                              let uu____666 =
                                FStar_Syntax_Syntax.bv_to_name a1  in
                              let uu____667 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____666, uu____667)  in
                            let uu____668 =
                              let uu____675 =
                                let uu____680 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (t, uu____680)  in
                              [uu____675]  in
                            uu____661 :: uu____668  in
                          FStar_List.append uu____621 uu____654  in
                        (fv, uu____614)  in
                      FStar_Syntax_Syntax.Tm_app uu____599  in
                    mk1 uu____598  in
                  (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
               in
            match uu____496 with
            | (env1,mk_ctx,mk_gctx) ->
                let c_pure =
                  let t =
                    FStar_Syntax_Syntax.gen_bv "t"
                      FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                     in
                  let x =
                    let uu____745 = FStar_Syntax_Syntax.bv_to_name t  in
                    FStar_Syntax_Syntax.gen_bv "x"
                      FStar_Pervasives_Native.None uu____745
                     in
                  let ret1 =
                    let uu____749 =
                      let uu____750 =
                        let uu____753 = FStar_Syntax_Syntax.bv_to_name t  in
                        mk_ctx uu____753  in
                      FStar_Syntax_Util.residual_tot uu____750  in
                    FStar_Pervasives_Native.Some uu____749  in
                  let body =
                    let uu____755 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.abs gamma uu____755 ret1  in
                  let uu____756 =
                    let uu____757 = mk_all_implicit binders  in
                    let uu____764 =
                      binders_of_list1 [(a1, true); (t, true); (x, false)]
                       in
                    FStar_List.append uu____757 uu____764  in
                  FStar_Syntax_Util.abs uu____756 body ret1  in
                let c_pure1 =
                  let uu____792 = mk_lid "pure"  in
                  register env1 uu____792 c_pure  in
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
                    let uu____797 =
                      let uu____798 =
                        let uu____799 =
                          let uu____806 =
                            let uu____807 =
                              let uu____808 =
                                FStar_Syntax_Syntax.bv_to_name t1  in
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None uu____808
                               in
                            FStar_Syntax_Syntax.mk_binder uu____807  in
                          [uu____806]  in
                        let uu____809 =
                          let uu____812 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          FStar_Syntax_Syntax.mk_GTotal uu____812  in
                        FStar_Syntax_Util.arrow uu____799 uu____809  in
                      mk_gctx uu____798  in
                    FStar_Syntax_Syntax.gen_bv "l"
                      FStar_Pervasives_Native.None uu____797
                     in
                  let r =
                    let uu____814 =
                      let uu____815 = FStar_Syntax_Syntax.bv_to_name t1  in
                      mk_gctx uu____815  in
                    FStar_Syntax_Syntax.gen_bv "r"
                      FStar_Pervasives_Native.None uu____814
                     in
                  let ret1 =
                    let uu____819 =
                      let uu____820 =
                        let uu____823 = FStar_Syntax_Syntax.bv_to_name t2  in
                        mk_gctx uu____823  in
                      FStar_Syntax_Util.residual_tot uu____820  in
                    FStar_Pervasives_Native.Some uu____819  in
                  let outer_body =
                    let gamma_as_args = args_of_binders1 gamma  in
                    let inner_body =
                      let uu____831 = FStar_Syntax_Syntax.bv_to_name l  in
                      let uu____834 =
                        let uu____843 =
                          let uu____846 =
                            let uu____847 =
                              let uu____848 =
                                FStar_Syntax_Syntax.bv_to_name r  in
                              FStar_Syntax_Util.mk_app uu____848
                                gamma_as_args
                               in
                            FStar_Syntax_Syntax.as_arg uu____847  in
                          [uu____846]  in
                        FStar_List.append gamma_as_args uu____843  in
                      FStar_Syntax_Util.mk_app uu____831 uu____834  in
                    FStar_Syntax_Util.abs gamma inner_body ret1  in
                  let uu____851 =
                    let uu____852 = mk_all_implicit binders  in
                    let uu____859 =
                      binders_of_list1
                        [(a1, true);
                        (t1, true);
                        (t2, true);
                        (l, false);
                        (r, false)]
                       in
                    FStar_List.append uu____852 uu____859  in
                  FStar_Syntax_Util.abs uu____851 outer_body ret1  in
                let c_app1 =
                  let uu____895 = mk_lid "app"  in
                  register env1 uu____895 c_app  in
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
                    let uu____902 =
                      let uu____909 =
                        let uu____910 = FStar_Syntax_Syntax.bv_to_name t1  in
                        FStar_Syntax_Syntax.null_binder uu____910  in
                      [uu____909]  in
                    let uu____911 =
                      let uu____914 = FStar_Syntax_Syntax.bv_to_name t2  in
                      FStar_Syntax_Syntax.mk_GTotal uu____914  in
                    FStar_Syntax_Util.arrow uu____902 uu____911  in
                  let f =
                    FStar_Syntax_Syntax.gen_bv "f"
                      FStar_Pervasives_Native.None t_f
                     in
                  let a11 =
                    let uu____917 =
                      let uu____918 = FStar_Syntax_Syntax.bv_to_name t1  in
                      mk_gctx uu____918  in
                    FStar_Syntax_Syntax.gen_bv "a1"
                      FStar_Pervasives_Native.None uu____917
                     in
                  let ret1 =
                    let uu____922 =
                      let uu____923 =
                        let uu____926 = FStar_Syntax_Syntax.bv_to_name t2  in
                        mk_gctx uu____926  in
                      FStar_Syntax_Util.residual_tot uu____923  in
                    FStar_Pervasives_Native.Some uu____922  in
                  let uu____927 =
                    let uu____928 = mk_all_implicit binders  in
                    let uu____935 =
                      binders_of_list1
                        [(a1, true);
                        (t1, true);
                        (t2, true);
                        (f, false);
                        (a11, false)]
                       in
                    FStar_List.append uu____928 uu____935  in
                  let uu____970 =
                    let uu____971 =
                      let uu____980 =
                        let uu____983 =
                          let uu____986 =
                            let uu____995 =
                              let uu____998 =
                                FStar_Syntax_Syntax.bv_to_name f  in
                              [uu____998]  in
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              uu____995
                             in
                          FStar_Syntax_Util.mk_app c_pure1 uu____986  in
                        let uu____999 =
                          let uu____1004 = FStar_Syntax_Syntax.bv_to_name a11
                             in
                          [uu____1004]  in
                        uu____983 :: uu____999  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____980  in
                    FStar_Syntax_Util.mk_app c_app1 uu____971  in
                  FStar_Syntax_Util.abs uu____927 uu____970 ret1  in
                let c_lift11 =
                  let uu____1008 = mk_lid "lift1"  in
                  register env1 uu____1008 c_lift1  in
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
                    let uu____1016 =
                      let uu____1023 =
                        let uu____1024 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        FStar_Syntax_Syntax.null_binder uu____1024  in
                      let uu____1025 =
                        let uu____1028 =
                          let uu____1029 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          FStar_Syntax_Syntax.null_binder uu____1029  in
                        [uu____1028]  in
                      uu____1023 :: uu____1025  in
                    let uu____1030 =
                      let uu____1033 = FStar_Syntax_Syntax.bv_to_name t3  in
                      FStar_Syntax_Syntax.mk_GTotal uu____1033  in
                    FStar_Syntax_Util.arrow uu____1016 uu____1030  in
                  let f =
                    FStar_Syntax_Syntax.gen_bv "f"
                      FStar_Pervasives_Native.None t_f
                     in
                  let a11 =
                    let uu____1036 =
                      let uu____1037 = FStar_Syntax_Syntax.bv_to_name t1  in
                      mk_gctx uu____1037  in
                    FStar_Syntax_Syntax.gen_bv "a1"
                      FStar_Pervasives_Native.None uu____1036
                     in
                  let a2 =
                    let uu____1039 =
                      let uu____1040 = FStar_Syntax_Syntax.bv_to_name t2  in
                      mk_gctx uu____1040  in
                    FStar_Syntax_Syntax.gen_bv "a2"
                      FStar_Pervasives_Native.None uu____1039
                     in
                  let ret1 =
                    let uu____1044 =
                      let uu____1045 =
                        let uu____1048 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        mk_gctx uu____1048  in
                      FStar_Syntax_Util.residual_tot uu____1045  in
                    FStar_Pervasives_Native.Some uu____1044  in
                  let uu____1049 =
                    let uu____1050 = mk_all_implicit binders  in
                    let uu____1057 =
                      binders_of_list1
                        [(a1, true);
                        (t1, true);
                        (t2, true);
                        (t3, true);
                        (f, false);
                        (a11, false);
                        (a2, false)]
                       in
                    FStar_List.append uu____1050 uu____1057  in
                  let uu____1100 =
                    let uu____1101 =
                      let uu____1110 =
                        let uu____1113 =
                          let uu____1116 =
                            let uu____1125 =
                              let uu____1128 =
                                let uu____1131 =
                                  let uu____1140 =
                                    let uu____1143 =
                                      FStar_Syntax_Syntax.bv_to_name f  in
                                    [uu____1143]  in
                                  FStar_List.map FStar_Syntax_Syntax.as_arg
                                    uu____1140
                                   in
                                FStar_Syntax_Util.mk_app c_pure1 uu____1131
                                 in
                              let uu____1144 =
                                let uu____1149 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                [uu____1149]  in
                              uu____1128 :: uu____1144  in
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              uu____1125
                             in
                          FStar_Syntax_Util.mk_app c_app1 uu____1116  in
                        let uu____1152 =
                          let uu____1157 = FStar_Syntax_Syntax.bv_to_name a2
                             in
                          [uu____1157]  in
                        uu____1113 :: uu____1152  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____1110
                       in
                    FStar_Syntax_Util.mk_app c_app1 uu____1101  in
                  FStar_Syntax_Util.abs uu____1049 uu____1100 ret1  in
                let c_lift21 =
                  let uu____1161 = mk_lid "lift2"  in
                  register env1 uu____1161 c_lift2  in
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
                    let uu____1168 =
                      let uu____1175 =
                        let uu____1176 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        FStar_Syntax_Syntax.null_binder uu____1176  in
                      [uu____1175]  in
                    let uu____1177 =
                      let uu____1180 =
                        let uu____1181 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1181  in
                      FStar_Syntax_Syntax.mk_Total uu____1180  in
                    FStar_Syntax_Util.arrow uu____1168 uu____1177  in
                  let f =
                    FStar_Syntax_Syntax.gen_bv "f"
                      FStar_Pervasives_Native.None t_f
                     in
                  let ret1 =
                    let uu____1186 =
                      let uu____1187 =
                        let uu____1190 =
                          let uu____1191 =
                            let uu____1198 =
                              let uu____1199 =
                                FStar_Syntax_Syntax.bv_to_name t1  in
                              FStar_Syntax_Syntax.null_binder uu____1199  in
                            [uu____1198]  in
                          let uu____1200 =
                            let uu____1203 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.mk_GTotal uu____1203  in
                          FStar_Syntax_Util.arrow uu____1191 uu____1200  in
                        mk_ctx uu____1190  in
                      FStar_Syntax_Util.residual_tot uu____1187  in
                    FStar_Pervasives_Native.Some uu____1186  in
                  let e1 =
                    let uu____1205 = FStar_Syntax_Syntax.bv_to_name t1  in
                    FStar_Syntax_Syntax.gen_bv "e1"
                      FStar_Pervasives_Native.None uu____1205
                     in
                  let body =
                    let uu____1207 =
                      let uu____1208 =
                        let uu____1215 = FStar_Syntax_Syntax.mk_binder e1  in
                        [uu____1215]  in
                      FStar_List.append gamma uu____1208  in
                    let uu____1220 =
                      let uu____1221 = FStar_Syntax_Syntax.bv_to_name f  in
                      let uu____1224 =
                        let uu____1233 =
                          let uu____1234 = FStar_Syntax_Syntax.bv_to_name e1
                             in
                          FStar_Syntax_Syntax.as_arg uu____1234  in
                        let uu____1235 = args_of_binders1 gamma  in
                        uu____1233 :: uu____1235  in
                      FStar_Syntax_Util.mk_app uu____1221 uu____1224  in
                    FStar_Syntax_Util.abs uu____1207 uu____1220 ret1  in
                  let uu____1238 =
                    let uu____1239 = mk_all_implicit binders  in
                    let uu____1246 =
                      binders_of_list1
                        [(a1, true); (t1, true); (t2, true); (f, false)]
                       in
                    FStar_List.append uu____1239 uu____1246  in
                  FStar_Syntax_Util.abs uu____1238 body ret1  in
                let c_push1 =
                  let uu____1278 = mk_lid "push"  in
                  register env1 uu____1278 c_push  in
                let ret_tot_wp_a =
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_tot wp_a1)
                   in
                let mk_generic_app c =
                  if (FStar_List.length binders) > (Prims.parse_int "0")
                  then
                    let uu____1300 =
                      let uu____1301 =
                        let uu____1316 = args_of_binders1 binders  in
                        (c, uu____1316)  in
                      FStar_Syntax_Syntax.Tm_app uu____1301  in
                    mk1 uu____1300
                  else c  in
                let wp_if_then_else =
                  let result_comp =
                    let uu____1326 =
                      let uu____1327 =
                        let uu____1334 =
                          FStar_Syntax_Syntax.null_binder wp_a1  in
                        let uu____1335 =
                          let uu____1338 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          [uu____1338]  in
                        uu____1334 :: uu____1335  in
                      let uu____1339 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1327 uu____1339  in
                    FStar_Syntax_Syntax.mk_Total uu____1326  in
                  let c =
                    FStar_Syntax_Syntax.gen_bv "c"
                      FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                     in
                  let uu____1343 =
                    let uu____1344 =
                      FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                    FStar_List.append binders uu____1344  in
                  let uu____1355 =
                    let l_ite =
                      FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                        (FStar_Syntax_Syntax.Delta_defined_at_level
                           (Prims.parse_int "2"))
                        FStar_Pervasives_Native.None
                       in
                    let uu____1357 =
                      let uu____1360 =
                        let uu____1369 =
                          let uu____1372 =
                            let uu____1375 =
                              let uu____1384 =
                                let uu____1385 =
                                  FStar_Syntax_Syntax.bv_to_name c  in
                                FStar_Syntax_Syntax.as_arg uu____1385  in
                              [uu____1384]  in
                            FStar_Syntax_Util.mk_app l_ite uu____1375  in
                          [uu____1372]  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1369
                         in
                      FStar_Syntax_Util.mk_app c_lift21 uu____1360  in
                    FStar_Syntax_Util.ascribe uu____1357
                      ((FStar_Util.Inr result_comp),
                        FStar_Pervasives_Native.None)
                     in
                  FStar_Syntax_Util.abs uu____1343 uu____1355
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                   in
                let wp_if_then_else1 =
                  let uu____1405 = mk_lid "wp_if_then_else"  in
                  register env1 uu____1405 wp_if_then_else  in
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
                    let uu____1416 =
                      let uu____1425 =
                        let uu____1428 =
                          let uu____1431 =
                            let uu____1440 =
                              let uu____1443 =
                                let uu____1446 =
                                  let uu____1455 =
                                    let uu____1456 =
                                      FStar_Syntax_Syntax.bv_to_name q  in
                                    FStar_Syntax_Syntax.as_arg uu____1456  in
                                  [uu____1455]  in
                                FStar_Syntax_Util.mk_app l_and uu____1446  in
                              [uu____1443]  in
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              uu____1440
                             in
                          FStar_Syntax_Util.mk_app c_pure1 uu____1431  in
                        let uu____1461 =
                          let uu____1466 = FStar_Syntax_Syntax.bv_to_name wp
                             in
                          [uu____1466]  in
                        uu____1428 :: uu____1461  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____1425
                       in
                    FStar_Syntax_Util.mk_app c_app1 uu____1416  in
                  let uu____1469 =
                    let uu____1470 =
                      FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                    FStar_List.append binders uu____1470  in
                  FStar_Syntax_Util.abs uu____1469 body ret_tot_wp_a  in
                let wp_assert1 =
                  let uu____1482 = mk_lid "wp_assert"  in
                  register env1 uu____1482 wp_assert  in
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
                    let uu____1493 =
                      let uu____1502 =
                        let uu____1505 =
                          let uu____1508 =
                            let uu____1517 =
                              let uu____1520 =
                                let uu____1523 =
                                  let uu____1532 =
                                    let uu____1533 =
                                      FStar_Syntax_Syntax.bv_to_name q  in
                                    FStar_Syntax_Syntax.as_arg uu____1533  in
                                  [uu____1532]  in
                                FStar_Syntax_Util.mk_app l_imp uu____1523  in
                              [uu____1520]  in
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              uu____1517
                             in
                          FStar_Syntax_Util.mk_app c_pure1 uu____1508  in
                        let uu____1538 =
                          let uu____1543 = FStar_Syntax_Syntax.bv_to_name wp
                             in
                          [uu____1543]  in
                        uu____1505 :: uu____1538  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____1502
                       in
                    FStar_Syntax_Util.mk_app c_app1 uu____1493  in
                  let uu____1546 =
                    let uu____1547 =
                      FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                    FStar_List.append binders uu____1547  in
                  FStar_Syntax_Util.abs uu____1546 body ret_tot_wp_a  in
                let wp_assume1 =
                  let uu____1559 = mk_lid "wp_assume"  in
                  register env1 uu____1559 wp_assume  in
                let wp_assume2 = mk_generic_app wp_assume1  in
                let wp_close =
                  let b =
                    FStar_Syntax_Syntax.gen_bv "b"
                      FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                     in
                  let t_f =
                    let uu____1568 =
                      let uu____1575 =
                        let uu____1576 = FStar_Syntax_Syntax.bv_to_name b  in
                        FStar_Syntax_Syntax.null_binder uu____1576  in
                      [uu____1575]  in
                    let uu____1577 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                    FStar_Syntax_Util.arrow uu____1568 uu____1577  in
                  let f =
                    FStar_Syntax_Syntax.gen_bv "f"
                      FStar_Pervasives_Native.None t_f
                     in
                  let body =
                    let uu____1584 =
                      let uu____1593 =
                        let uu____1596 =
                          let uu____1599 =
                            FStar_List.map FStar_Syntax_Syntax.as_arg
                              [FStar_Syntax_Util.tforall]
                             in
                          FStar_Syntax_Util.mk_app c_pure1 uu____1599  in
                        let uu____1608 =
                          let uu____1613 =
                            let uu____1616 =
                              let uu____1625 =
                                let uu____1628 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1628]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1625
                               in
                            FStar_Syntax_Util.mk_app c_push1 uu____1616  in
                          [uu____1613]  in
                        uu____1596 :: uu____1608  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____1593
                       in
                    FStar_Syntax_Util.mk_app c_app1 uu____1584  in
                  let uu____1635 =
                    let uu____1636 =
                      FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                    FStar_List.append binders uu____1636  in
                  FStar_Syntax_Util.abs uu____1635 body ret_tot_wp_a  in
                let wp_close1 =
                  let uu____1648 = mk_lid "wp_close"  in
                  register env1 uu____1648 wp_close  in
                let wp_close2 = mk_generic_app wp_close1  in
                let ret_tot_type =
                  FStar_Pervasives_Native.Some
                    (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                   in
                let ret_gtot_type =
                  let uu____1658 =
                    let uu____1659 =
                      let uu____1660 =
                        FStar_Syntax_Syntax.mk_GTotal FStar_Syntax_Util.ktype
                         in
                      FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                        uu____1660
                       in
                    FStar_Syntax_Util.residual_comp_of_lcomp uu____1659  in
                  FStar_Pervasives_Native.Some uu____1658  in
                let mk_forall1 x body =
                  let uu____1676 =
                    let uu____1683 =
                      let uu____1684 =
                        let uu____1699 =
                          let uu____1702 =
                            let uu____1703 =
                              let uu____1704 =
                                let uu____1705 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____1705]  in
                              FStar_Syntax_Util.abs uu____1704 body
                                ret_tot_type
                               in
                            FStar_Syntax_Syntax.as_arg uu____1703  in
                          [uu____1702]  in
                        (FStar_Syntax_Util.tforall, uu____1699)  in
                      FStar_Syntax_Syntax.Tm_app uu____1684  in
                    FStar_Syntax_Syntax.mk uu____1683  in
                  uu____1676 FStar_Pervasives_Native.None
                    FStar_Range.dummyRange
                   in
                let rec is_discrete t =
                  let uu____1717 =
                    let uu____1718 = FStar_Syntax_Subst.compress t  in
                    uu____1718.FStar_Syntax_Syntax.n  in
                  match uu____1717 with
                  | FStar_Syntax_Syntax.Tm_type uu____1721 -> false
                  | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                      (FStar_List.for_all
                         (fun uu____1747  ->
                            match uu____1747 with
                            | (b,uu____1753) ->
                                is_discrete b.FStar_Syntax_Syntax.sort) bs)
                        && (is_discrete (FStar_Syntax_Util.comp_result c))
                  | uu____1754 -> true  in
                let rec is_monotonic t =
                  let uu____1761 =
                    let uu____1762 = FStar_Syntax_Subst.compress t  in
                    uu____1762.FStar_Syntax_Syntax.n  in
                  match uu____1761 with
                  | FStar_Syntax_Syntax.Tm_type uu____1765 -> true
                  | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                      (FStar_List.for_all
                         (fun uu____1791  ->
                            match uu____1791 with
                            | (b,uu____1797) ->
                                is_discrete b.FStar_Syntax_Syntax.sort) bs)
                        && (is_monotonic (FStar_Syntax_Util.comp_result c))
                  | uu____1798 -> is_discrete t  in
                let rec mk_rel rel t x y =
                  let mk_rel1 = mk_rel rel  in
                  let t1 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta;
                      FStar_TypeChecker_Normalize.Eager_unfolding;
                      FStar_TypeChecker_Normalize.UnfoldUntil
                        FStar_Syntax_Syntax.Delta_constant] env1 t
                     in
                  let uu____1864 =
                    let uu____1865 = FStar_Syntax_Subst.compress t1  in
                    uu____1865.FStar_Syntax_Syntax.n  in
                  match uu____1864 with
                  | FStar_Syntax_Syntax.Tm_type uu____1868 -> rel x y
                  | FStar_Syntax_Syntax.Tm_arrow
                      (binder::[],{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.GTotal
                                      (b,uu____1871);
                                    FStar_Syntax_Syntax.pos = uu____1872;
                                    FStar_Syntax_Syntax.vars = uu____1873;_})
                      ->
                      let a2 =
                        (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                         in
                      let uu____1907 = (is_monotonic a2) || (is_monotonic b)
                         in
                      if uu____1907
                      then
                        let a11 =
                          FStar_Syntax_Syntax.gen_bv "a1"
                            FStar_Pervasives_Native.None a2
                           in
                        let body =
                          let uu____1910 =
                            let uu____1913 =
                              let uu____1922 =
                                let uu____1923 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                FStar_Syntax_Syntax.as_arg uu____1923  in
                              [uu____1922]  in
                            FStar_Syntax_Util.mk_app x uu____1913  in
                          let uu____1924 =
                            let uu____1927 =
                              let uu____1936 =
                                let uu____1937 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                FStar_Syntax_Syntax.as_arg uu____1937  in
                              [uu____1936]  in
                            FStar_Syntax_Util.mk_app y uu____1927  in
                          mk_rel1 b uu____1910 uu____1924  in
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
                           let uu____1942 =
                             let uu____1943 =
                               FStar_Syntax_Syntax.bv_to_name a11  in
                             let uu____1946 =
                               FStar_Syntax_Syntax.bv_to_name a21  in
                             mk_rel1 a2 uu____1943 uu____1946  in
                           let uu____1949 =
                             let uu____1950 =
                               let uu____1953 =
                                 let uu____1962 =
                                   let uu____1963 =
                                     FStar_Syntax_Syntax.bv_to_name a11  in
                                   FStar_Syntax_Syntax.as_arg uu____1963  in
                                 [uu____1962]  in
                               FStar_Syntax_Util.mk_app x uu____1953  in
                             let uu____1964 =
                               let uu____1967 =
                                 let uu____1976 =
                                   let uu____1977 =
                                     FStar_Syntax_Syntax.bv_to_name a21  in
                                   FStar_Syntax_Syntax.as_arg uu____1977  in
                                 [uu____1976]  in
                               FStar_Syntax_Util.mk_app y uu____1967  in
                             mk_rel1 b uu____1950 uu____1964  in
                           FStar_Syntax_Util.mk_imp uu____1942 uu____1949  in
                         let uu____1978 = mk_forall1 a21 body  in
                         mk_forall1 a11 uu____1978)
                  | FStar_Syntax_Syntax.Tm_arrow
                      (binder::[],{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Total
                                      (b,uu____1981);
                                    FStar_Syntax_Syntax.pos = uu____1982;
                                    FStar_Syntax_Syntax.vars = uu____1983;_})
                      ->
                      let a2 =
                        (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                         in
                      let uu____2017 = (is_monotonic a2) || (is_monotonic b)
                         in
                      if uu____2017
                      then
                        let a11 =
                          FStar_Syntax_Syntax.gen_bv "a1"
                            FStar_Pervasives_Native.None a2
                           in
                        let body =
                          let uu____2020 =
                            let uu____2023 =
                              let uu____2032 =
                                let uu____2033 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                FStar_Syntax_Syntax.as_arg uu____2033  in
                              [uu____2032]  in
                            FStar_Syntax_Util.mk_app x uu____2023  in
                          let uu____2034 =
                            let uu____2037 =
                              let uu____2046 =
                                let uu____2047 =
                                  FStar_Syntax_Syntax.bv_to_name a11  in
                                FStar_Syntax_Syntax.as_arg uu____2047  in
                              [uu____2046]  in
                            FStar_Syntax_Util.mk_app y uu____2037  in
                          mk_rel1 b uu____2020 uu____2034  in
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
                           let uu____2052 =
                             let uu____2053 =
                               FStar_Syntax_Syntax.bv_to_name a11  in
                             let uu____2056 =
                               FStar_Syntax_Syntax.bv_to_name a21  in
                             mk_rel1 a2 uu____2053 uu____2056  in
                           let uu____2059 =
                             let uu____2060 =
                               let uu____2063 =
                                 let uu____2072 =
                                   let uu____2073 =
                                     FStar_Syntax_Syntax.bv_to_name a11  in
                                   FStar_Syntax_Syntax.as_arg uu____2073  in
                                 [uu____2072]  in
                               FStar_Syntax_Util.mk_app x uu____2063  in
                             let uu____2074 =
                               let uu____2077 =
                                 let uu____2086 =
                                   let uu____2087 =
                                     FStar_Syntax_Syntax.bv_to_name a21  in
                                   FStar_Syntax_Syntax.as_arg uu____2087  in
                                 [uu____2086]  in
                               FStar_Syntax_Util.mk_app y uu____2077  in
                             mk_rel1 b uu____2060 uu____2074  in
                           FStar_Syntax_Util.mk_imp uu____2052 uu____2059  in
                         let uu____2088 = mk_forall1 a21 body  in
                         mk_forall1 a11 uu____2088)
                  | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                      let t2 =
                        let uu___78_2119 = t1  in
                        let uu____2120 =
                          let uu____2121 =
                            let uu____2134 =
                              let uu____2135 =
                                FStar_Syntax_Util.arrow binders1 comp  in
                              FStar_Syntax_Syntax.mk_Total uu____2135  in
                            ([binder], uu____2134)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____2121  in
                        {
                          FStar_Syntax_Syntax.n = uu____2120;
                          FStar_Syntax_Syntax.pos =
                            (uu___78_2119.FStar_Syntax_Syntax.pos);
                          FStar_Syntax_Syntax.vars =
                            (uu___78_2119.FStar_Syntax_Syntax.vars)
                        }  in
                      mk_rel1 t2 x y
                  | FStar_Syntax_Syntax.Tm_arrow uu____2150 ->
                      failwith "unhandled arrow"
                  | uu____2163 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                    let uu____2184 =
                      let uu____2185 = FStar_Syntax_Subst.compress t1  in
                      uu____2185.FStar_Syntax_Syntax.n  in
                    match uu____2184 with
                    | FStar_Syntax_Syntax.Tm_type uu____2188 ->
                        FStar_Syntax_Util.mk_imp x y
                    | FStar_Syntax_Syntax.Tm_app (head1,args) when
                        let uu____2211 = FStar_Syntax_Subst.compress head1
                           in
                        FStar_Syntax_Util.is_tuple_constructor uu____2211 ->
                        let project i tuple =
                          let projector =
                            let uu____2230 =
                              let uu____2231 =
                                FStar_Parser_Const.mk_tuple_data_lid
                                  (FStar_List.length args)
                                  FStar_Range.dummyRange
                                 in
                              FStar_TypeChecker_Env.lookup_projector env1
                                uu____2231 i
                               in
                            FStar_Syntax_Syntax.fvar uu____2230
                              (FStar_Syntax_Syntax.Delta_defined_at_level
                                 (Prims.parse_int "1"))
                              FStar_Pervasives_Native.None
                             in
                          FStar_Syntax_Util.mk_app projector
                            [(tuple, FStar_Pervasives_Native.None)]
                           in
                        let uu____2258 =
                          let uu____2265 =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2279  ->
                                   match uu____2279 with
                                   | (t2,q) ->
                                       let uu____2286 = project i x  in
                                       let uu____2287 = project i y  in
                                       mk_stronger t2 uu____2286 uu____2287)
                              args
                             in
                          match uu____2265 with
                          | [] ->
                              failwith
                                "Impossible : Empty application when creating stronger relation in DM4F"
                          | rel0::rels -> (rel0, rels)  in
                        (match uu____2258 with
                         | (rel0,rels) ->
                             FStar_List.fold_left FStar_Syntax_Util.mk_conj
                               rel0 rels)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binders1,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.GTotal
                                      (b,uu____2314);
                                    FStar_Syntax_Syntax.pos = uu____2315;
                                    FStar_Syntax_Syntax.vars = uu____2316;_})
                        ->
                        let bvs =
                          FStar_List.mapi
                            (fun i  ->
                               fun uu____2354  ->
                                 match uu____2354 with
                                 | (bv,q) ->
                                     let uu____2361 =
                                       let uu____2362 =
                                         FStar_Util.string_of_int i  in
                                       Prims.strcat "a" uu____2362  in
                                     FStar_Syntax_Syntax.gen_bv uu____2361
                                       FStar_Pervasives_Native.None
                                       bv.FStar_Syntax_Syntax.sort) binders1
                           in
                        let args =
                          FStar_List.map
                            (fun ai  ->
                               let uu____2369 =
                                 FStar_Syntax_Syntax.bv_to_name ai  in
                               FStar_Syntax_Syntax.as_arg uu____2369) bvs
                           in
                        let body =
                          let uu____2371 = FStar_Syntax_Util.mk_app x args
                             in
                          let uu____2372 = FStar_Syntax_Util.mk_app y args
                             in
                          mk_stronger b uu____2371 uu____2372  in
                        FStar_List.fold_right
                          (fun bv  -> fun body1  -> mk_forall1 bv body1) bvs
                          body
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binders1,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Total
                                      (b,uu____2379);
                                    FStar_Syntax_Syntax.pos = uu____2380;
                                    FStar_Syntax_Syntax.vars = uu____2381;_})
                        ->
                        let bvs =
                          FStar_List.mapi
                            (fun i  ->
                               fun uu____2419  ->
                                 match uu____2419 with
                                 | (bv,q) ->
                                     let uu____2426 =
                                       let uu____2427 =
                                         FStar_Util.string_of_int i  in
                                       Prims.strcat "a" uu____2427  in
                                     FStar_Syntax_Syntax.gen_bv uu____2426
                                       FStar_Pervasives_Native.None
                                       bv.FStar_Syntax_Syntax.sort) binders1
                           in
                        let args =
                          FStar_List.map
                            (fun ai  ->
                               let uu____2434 =
                                 FStar_Syntax_Syntax.bv_to_name ai  in
                               FStar_Syntax_Syntax.as_arg uu____2434) bvs
                           in
                        let body =
                          let uu____2436 = FStar_Syntax_Util.mk_app x args
                             in
                          let uu____2437 = FStar_Syntax_Util.mk_app y args
                             in
                          mk_stronger b uu____2436 uu____2437  in
                        FStar_List.fold_right
                          (fun bv  -> fun body1  -> mk_forall1 bv body1) bvs
                          body
                    | uu____2442 -> failwith "Not a DM elaborated type"  in
                  let body =
                    let uu____2444 = FStar_Syntax_Util.unascribe wp_a1  in
                    let uu____2445 = FStar_Syntax_Syntax.bv_to_name wp1  in
                    let uu____2446 = FStar_Syntax_Syntax.bv_to_name wp2  in
                    mk_stronger uu____2444 uu____2445 uu____2446  in
                  let uu____2447 =
                    let uu____2448 =
                      binders_of_list1
                        [(a1, false); (wp1, false); (wp2, false)]
                       in
                    FStar_List.append binders uu____2448  in
                  FStar_Syntax_Util.abs uu____2447 body ret_tot_type  in
                let stronger1 =
                  let uu____2476 = mk_lid "stronger"  in
                  register env1 uu____2476 stronger  in
                let stronger2 = mk_generic_app stronger1  in
                let wp_ite =
                  let wp =
                    FStar_Syntax_Syntax.gen_bv "wp"
                      FStar_Pervasives_Native.None wp_a1
                     in
                  let uu____2482 = FStar_Util.prefix gamma  in
                  match uu____2482 with
                  | (wp_args,post) ->
                      let k =
                        FStar_Syntax_Syntax.gen_bv "k"
                          FStar_Pervasives_Native.None
                          (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                         in
                      let equiv1 =
                        let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                        let eq1 =
                          let uu____2527 =
                            FStar_Syntax_Syntax.bv_to_name
                              (FStar_Pervasives_Native.fst post)
                             in
                          mk_rel FStar_Syntax_Util.mk_iff
                            k.FStar_Syntax_Syntax.sort k_tm uu____2527
                           in
                        let uu____2530 =
                          FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                        match uu____2530 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                            let k_app =
                              let uu____2540 = args_of_binders1 binders1  in
                              FStar_Syntax_Util.mk_app k_tm uu____2540  in
                            let guard_free1 =
                              let uu____2550 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.guard_free
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Syntax_Syntax.fv_to_tm uu____2550  in
                            let pat =
                              let uu____2554 =
                                let uu____2563 =
                                  FStar_Syntax_Syntax.as_arg k_app  in
                                [uu____2563]  in
                              FStar_Syntax_Util.mk_app guard_free1 uu____2554
                               in
                            let pattern_guarded_body =
                              let uu____2567 =
                                let uu____2568 =
                                  let uu____2575 =
                                    let uu____2576 =
                                      let uu____2587 =
                                        let uu____2590 =
                                          FStar_Syntax_Syntax.as_arg pat  in
                                        [uu____2590]  in
                                      [uu____2587]  in
                                    FStar_Syntax_Syntax.Meta_pattern
                                      uu____2576
                                     in
                                  (body, uu____2575)  in
                                FStar_Syntax_Syntax.Tm_meta uu____2568  in
                              mk1 uu____2567  in
                            FStar_Syntax_Util.close_forall_no_univs binders1
                              pattern_guarded_body
                        | uu____2595 ->
                            failwith
                              "Impossible: Expected the equivalence to be a quantified formula"
                         in
                      let body =
                        let uu____2599 =
                          let uu____2600 =
                            let uu____2601 =
                              let uu____2602 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              let uu____2605 =
                                let uu____2614 = args_of_binders1 wp_args  in
                                let uu____2617 =
                                  let uu____2620 =
                                    let uu____2621 =
                                      FStar_Syntax_Syntax.bv_to_name k  in
                                    FStar_Syntax_Syntax.as_arg uu____2621  in
                                  [uu____2620]  in
                                FStar_List.append uu____2614 uu____2617  in
                              FStar_Syntax_Util.mk_app uu____2602 uu____2605
                               in
                            FStar_Syntax_Util.mk_imp equiv1 uu____2601  in
                          FStar_Syntax_Util.mk_forall_no_univ k uu____2600
                           in
                        FStar_Syntax_Util.abs gamma uu____2599 ret_gtot_type
                         in
                      let uu____2622 =
                        let uu____2623 =
                          FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                        FStar_List.append binders uu____2623  in
                      FStar_Syntax_Util.abs uu____2622 body ret_gtot_type
                   in
                let wp_ite1 =
                  let uu____2635 = mk_lid "wp_ite"  in
                  register env1 uu____2635 wp_ite  in
                let wp_ite2 = mk_generic_app wp_ite1  in
                let null_wp =
                  let wp =
                    FStar_Syntax_Syntax.gen_bv "wp"
                      FStar_Pervasives_Native.None wp_a1
                     in
                  let uu____2641 = FStar_Util.prefix gamma  in
                  match uu____2641 with
                  | (wp_args,post) ->
                      let x =
                        FStar_Syntax_Syntax.gen_bv "x"
                          FStar_Pervasives_Native.None
                          FStar_Syntax_Syntax.tun
                         in
                      let body =
                        let uu____2684 =
                          let uu____2685 =
                            FStar_All.pipe_left
                              FStar_Syntax_Syntax.bv_to_name
                              (FStar_Pervasives_Native.fst post)
                             in
                          let uu____2688 =
                            let uu____2697 =
                              let uu____2698 =
                                FStar_Syntax_Syntax.bv_to_name x  in
                              FStar_Syntax_Syntax.as_arg uu____2698  in
                            [uu____2697]  in
                          FStar_Syntax_Util.mk_app uu____2685 uu____2688  in
                        FStar_Syntax_Util.mk_forall_no_univ x uu____2684  in
                      let uu____2699 =
                        let uu____2700 =
                          let uu____2707 =
                            FStar_Syntax_Syntax.binders_of_list [a1]  in
                          FStar_List.append uu____2707 gamma  in
                        FStar_List.append binders uu____2700  in
                      FStar_Syntax_Util.abs uu____2699 body ret_gtot_type
                   in
                let null_wp1 =
                  let uu____2723 = mk_lid "null_wp"  in
                  register env1 uu____2723 null_wp  in
                let null_wp2 = mk_generic_app null_wp1  in
                let wp_trivial =
                  let wp =
                    FStar_Syntax_Syntax.gen_bv "wp"
                      FStar_Pervasives_Native.None wp_a1
                     in
                  let body =
                    let uu____2732 =
                      let uu____2741 =
                        let uu____2744 = FStar_Syntax_Syntax.bv_to_name a1
                           in
                        let uu____2745 =
                          let uu____2748 =
                            let uu____2751 =
                              let uu____2760 =
                                let uu____2761 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                FStar_Syntax_Syntax.as_arg uu____2761  in
                              [uu____2760]  in
                            FStar_Syntax_Util.mk_app null_wp2 uu____2751  in
                          let uu____2762 =
                            let uu____2767 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____2767]  in
                          uu____2748 :: uu____2762  in
                        uu____2744 :: uu____2745  in
                      FStar_List.map FStar_Syntax_Syntax.as_arg uu____2741
                       in
                    FStar_Syntax_Util.mk_app stronger2 uu____2732  in
                  let uu____2770 =
                    let uu____2771 =
                      FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                    FStar_List.append binders uu____2771  in
                  FStar_Syntax_Util.abs uu____2770 body ret_tot_type  in
                let wp_trivial1 =
                  let uu____2783 = mk_lid "wp_trivial"  in
                  register env1 uu____2783 wp_trivial  in
                let wp_trivial2 = mk_generic_app wp_trivial1  in
                let uu____2787 =
                  let uu____2788 =
                    FStar_TypeChecker_Env.debug env1
                      (FStar_Options.Other "ED")
                     in
                  if uu____2788 then d "End Dijkstra monads for free" else ()
                   in
                let c = FStar_Syntax_Subst.close binders  in
                let uu____2795 =
                  let uu____2798 = FStar_ST.op_Bang sigelts  in
                  FStar_List.rev uu____2798  in
                let uu____2850 =
                  let uu___79_2851 = ed  in
                  let uu____2852 =
                    let uu____2853 = c wp_if_then_else2  in ([], uu____2853)
                     in
                  let uu____2856 =
                    let uu____2857 = c wp_ite2  in ([], uu____2857)  in
                  let uu____2860 =
                    let uu____2861 = c stronger2  in ([], uu____2861)  in
                  let uu____2864 =
                    let uu____2865 = c wp_close2  in ([], uu____2865)  in
                  let uu____2868 =
                    let uu____2869 = c wp_assert2  in ([], uu____2869)  in
                  let uu____2872 =
                    let uu____2873 = c wp_assume2  in ([], uu____2873)  in
                  let uu____2876 =
                    let uu____2877 = c null_wp2  in ([], uu____2877)  in
                  let uu____2880 =
                    let uu____2881 = c wp_trivial2  in ([], uu____2881)  in
                  {
                    FStar_Syntax_Syntax.cattributes =
                      (uu___79_2851.FStar_Syntax_Syntax.cattributes);
                    FStar_Syntax_Syntax.mname =
                      (uu___79_2851.FStar_Syntax_Syntax.mname);
                    FStar_Syntax_Syntax.univs =
                      (uu___79_2851.FStar_Syntax_Syntax.univs);
                    FStar_Syntax_Syntax.binders =
                      (uu___79_2851.FStar_Syntax_Syntax.binders);
                    FStar_Syntax_Syntax.signature =
                      (uu___79_2851.FStar_Syntax_Syntax.signature);
                    FStar_Syntax_Syntax.ret_wp =
                      (uu___79_2851.FStar_Syntax_Syntax.ret_wp);
                    FStar_Syntax_Syntax.bind_wp =
                      (uu___79_2851.FStar_Syntax_Syntax.bind_wp);
                    FStar_Syntax_Syntax.if_then_else = uu____2852;
                    FStar_Syntax_Syntax.ite_wp = uu____2856;
                    FStar_Syntax_Syntax.stronger = uu____2860;
                    FStar_Syntax_Syntax.close_wp = uu____2864;
                    FStar_Syntax_Syntax.assert_p = uu____2868;
                    FStar_Syntax_Syntax.assume_p = uu____2872;
                    FStar_Syntax_Syntax.null_wp = uu____2876;
                    FStar_Syntax_Syntax.trivial = uu____2880;
                    FStar_Syntax_Syntax.repr =
                      (uu___79_2851.FStar_Syntax_Syntax.repr);
                    FStar_Syntax_Syntax.return_repr =
                      (uu___79_2851.FStar_Syntax_Syntax.return_repr);
                    FStar_Syntax_Syntax.bind_repr =
                      (uu___79_2851.FStar_Syntax_Syntax.bind_repr);
                    FStar_Syntax_Syntax.actions =
                      (uu___79_2851.FStar_Syntax_Syntax.actions);
                    FStar_Syntax_Syntax.eff_attrs =
                      (uu___79_2851.FStar_Syntax_Syntax.eff_attrs)
                  }  in
                (uu____2795, uu____2850)
  
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___80_2901 = dmff_env  in
      {
        env = env';
        subst = (uu___80_2901.subst);
        tc_const = (uu___80_2901.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____2916 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____2930 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___66_2942  ->
    match uu___66_2942 with
    | FStar_Syntax_Syntax.Total (t,uu____2944) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___65_2957  ->
                match uu___65_2957 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2958 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2960 =
          let uu____2961 =
            let uu____2962 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2962
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2961  in
        failwith uu____2960
    | FStar_Syntax_Syntax.GTotal uu____2963 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___67_2976  ->
    match uu___67_2976 with
    | N t ->
        let uu____2978 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2978
    | M t ->
        let uu____2980 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2980
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2986,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2988;
                      FStar_Syntax_Syntax.vars = uu____2989;_})
        -> nm_of_comp n2
    | uu____3006 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____3016 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____3016 with | M uu____3017 -> true | N uu____3018 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3024 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____3038 =
        let uu____3045 =
          let uu____3046 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3046  in
        [uu____3045]  in
      let uu____3047 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3038 uu____3047  in
    let uu____3050 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3050
  
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
        mk1
          (let uu____3097 =
             let uu____3110 =
               let uu____3117 =
                 let uu____3122 =
                   let uu____3123 = star_type' env a  in
                   FStar_Syntax_Syntax.null_bv uu____3123  in
                 let uu____3124 = FStar_Syntax_Syntax.as_implicit false  in
                 (uu____3122, uu____3124)  in
               [uu____3117]  in
             let uu____3133 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
             (uu____3110, uu____3133)  in
           FStar_Syntax_Syntax.Tm_arrow uu____3097)

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3174) ->
          let binders1 =
            FStar_List.map
              (fun uu____3210  ->
                 match uu____3210 with
                 | (bv,aqual) ->
                     let uu____3221 =
                       let uu___81_3222 = bv  in
                       let uu____3223 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___81_3222.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___81_3222.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3223
                       }  in
                     (uu____3221, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3226,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3228);
                             FStar_Syntax_Syntax.pos = uu____3229;
                             FStar_Syntax_Syntax.vars = uu____3230;_})
               ->
               let uu____3255 =
                 let uu____3256 =
                   let uu____3269 =
                     let uu____3270 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3270  in
                   (binders1, uu____3269)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3256  in
               mk1 uu____3255
           | uu____3277 ->
               let uu____3278 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3278 with
                | N hn ->
                    let uu____3280 =
                      let uu____3281 =
                        let uu____3294 =
                          let uu____3295 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3295  in
                        (binders1, uu____3294)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3281  in
                    mk1 uu____3280
                | M a ->
                    let uu____3303 =
                      let uu____3304 =
                        let uu____3317 =
                          let uu____3324 =
                            let uu____3331 =
                              let uu____3336 =
                                let uu____3337 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____3337  in
                              let uu____3338 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____3336, uu____3338)  in
                            [uu____3331]  in
                          FStar_List.append binders1 uu____3324  in
                        let uu____3351 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____3317, uu____3351)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3304  in
                    mk1 uu____3303))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  let uu____3427 = FStar_Util.string_builder_append strb "{"
                     in
                  let uu____3428 =
                    let uu____3429 = f x  in
                    FStar_Util.string_builder_append strb uu____3429  in
                  let uu____3430 =
                    FStar_List.iter
                      (fun x1  ->
                         let uu____3435 =
                           FStar_Util.string_builder_append strb ", "  in
                         let uu____3436 = f x1  in
                         FStar_Util.string_builder_append strb uu____3436) xs
                     in
                  let uu____3437 = FStar_Util.string_builder_append strb "}"
                     in
                  FStar_Util.string_of_string_builder strb
               in
            let uu____3438 =
              let uu____3443 =
                let uu____3444 = FStar_Syntax_Print.term_to_string t2  in
                let uu____3445 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3444 uu____3445
                 in
              (FStar_Errors.Warning_DependencyFound, uu____3443)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3438  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3457 =
              let uu____3458 = FStar_Syntax_Subst.compress ty  in
              uu____3458.FStar_Syntax_Syntax.n  in
            match uu____3457 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3479 =
                  let uu____3480 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____3480  in
                if uu____3479
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3510 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____3510 s  in
                       let uu____3513 =
                         let uu____3514 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____3514  in
                       if uu____3513
                       then
                         let uu____3515 = debug1 ty1 sinter  in
                         FStar_Exn.raise Not_found
                       else ()  in
                     let uu____3517 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____3517 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3539  ->
                                  match uu____3539 with
                                  | (bv,uu____3549) ->
                                      let uu____3550 =
                                        non_dependent_or_raise s
                                          bv.FStar_Syntax_Syntax.sort
                                         in
                                      FStar_Util.set_add bv s)
                             FStar_Syntax_Syntax.no_names binders1
                            in
                         let ct = FStar_Syntax_Util.comp_result c1  in
                         let uu____3554 = non_dependent_or_raise s ct  in
                         let k = n1 - (FStar_List.length binders1)  in
                         if k > (Prims.parse_int "0")
                         then is_non_dependent_arrow ct k
                         else true
                   with | Not_found  -> false)
            | uu____3563 ->
                let uu____3564 =
                  let uu____3565 =
                    let uu____3570 =
                      let uu____3571 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3571
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3570)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3565
                   in
                false
             in
          let rec is_valid_application head2 =
            let uu____3578 =
              let uu____3579 = FStar_Syntax_Subst.compress head2  in
              uu____3579.FStar_Syntax_Syntax.n  in
            match uu____3578 with
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
                  (let uu____3584 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____3584)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3586 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____3586 with
                 | ((uu____3595,ty),uu____3597) ->
                     let uu____3602 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____3602
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1
                          in
                       let uu____3610 =
                         let uu____3611 = FStar_Syntax_Subst.compress res  in
                         uu____3611.FStar_Syntax_Syntax.n  in
                       (match uu____3610 with
                        | FStar_Syntax_Syntax.Tm_app uu____3614 -> true
                        | uu____3629 ->
                            let uu____3630 =
                              let uu____3631 =
                                let uu____3636 =
                                  let uu____3637 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3637
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3636)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3631
                               in
                            false)
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3639 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3640 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3642) ->
                is_valid_application t2
            | uu____3647 -> false  in
          let uu____3648 = is_valid_application head1  in
          if uu____3648
          then
            let uu____3649 =
              let uu____3650 =
                let uu____3665 =
                  FStar_List.map
                    (fun uu____3686  ->
                       match uu____3686 with
                       | (t2,qual) ->
                           let uu____3703 = star_type' env t2  in
                           (uu____3703, qual)) args
                   in
                (head1, uu____3665)  in
              FStar_Syntax_Syntax.Tm_app uu____3650  in
            mk1 uu____3649
          else
            (let uu____3713 =
               let uu____3718 =
                 let uu____3719 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3719
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____3718)  in
             FStar_Errors.raise_err uu____3713)
      | FStar_Syntax_Syntax.Tm_bvar uu____3720 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3721 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3722 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3723 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3747 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____3747 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___84_3755 = env  in
                 let uu____3756 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____3756;
                   subst = (uu___84_3755.subst);
                   tc_const = (uu___84_3755.tc_const)
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
               ((let uu___85_3776 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___85_3776.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___85_3776.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3783 =
            let uu____3784 =
              let uu____3791 = star_type' env t2  in (uu____3791, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____3784  in
          mk1 uu____3783
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3839 =
            let uu____3840 =
              let uu____3867 = star_type' env e  in
              let uu____3868 =
                let uu____3883 =
                  let uu____3890 = star_type' env t2  in
                  FStar_Util.Inl uu____3890  in
                (uu____3883, FStar_Pervasives_Native.None)  in
              (uu____3867, uu____3868, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3840  in
          mk1 uu____3839
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3968 =
            let uu____3969 =
              let uu____3996 = star_type' env e  in
              let uu____3997 =
                let uu____4012 =
                  let uu____4019 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____4019  in
                (uu____4012, FStar_Pervasives_Native.None)  in
              (uu____3996, uu____3997, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3969  in
          mk1 uu____3968
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4050,(uu____4051,FStar_Pervasives_Native.Some uu____4052),uu____4053)
          ->
          let uu____4102 =
            let uu____4107 =
              let uu____4108 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4108
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4107)  in
          FStar_Errors.raise_err uu____4102
      | FStar_Syntax_Syntax.Tm_refine uu____4109 ->
          let uu____4116 =
            let uu____4121 =
              let uu____4122 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4122
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4121)  in
          FStar_Errors.raise_err uu____4116
      | FStar_Syntax_Syntax.Tm_uinst uu____4123 ->
          let uu____4130 =
            let uu____4135 =
              let uu____4136 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4136
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4135)  in
          FStar_Errors.raise_err uu____4130
      | FStar_Syntax_Syntax.Tm_quoted uu____4137 ->
          let uu____4144 =
            let uu____4149 =
              let uu____4150 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4150
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4149)  in
          FStar_Errors.raise_err uu____4144
      | FStar_Syntax_Syntax.Tm_constant uu____4151 ->
          let uu____4152 =
            let uu____4157 =
              let uu____4158 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4158
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4157)  in
          FStar_Errors.raise_err uu____4152
      | FStar_Syntax_Syntax.Tm_match uu____4159 ->
          let uu____4182 =
            let uu____4187 =
              let uu____4188 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4188
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4187)  in
          FStar_Errors.raise_err uu____4182
      | FStar_Syntax_Syntax.Tm_let uu____4189 ->
          let uu____4202 =
            let uu____4207 =
              let uu____4208 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4208
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4207)  in
          FStar_Errors.raise_err uu____4202
      | FStar_Syntax_Syntax.Tm_uvar uu____4209 ->
          let uu____4226 =
            let uu____4231 =
              let uu____4232 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4232
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4231)  in
          FStar_Errors.raise_err uu____4226
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4233 =
            let uu____4238 =
              let uu____4239 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4239
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4238)  in
          FStar_Errors.raise_err uu____4233
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4241 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____4241
      | FStar_Syntax_Syntax.Tm_delayed uu____4244 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___69_4275  ->
    match uu___69_4275 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___68_4282  ->
                match uu___68_4282 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4283 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____4289 =
      let uu____4290 = FStar_Syntax_Subst.compress t  in
      uu____4290.FStar_Syntax_Syntax.n  in
    match uu____4289 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4316 =
            let uu____4317 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____4317  in
          is_C uu____4316  in
        if r
        then
          let uu____4332 =
            let uu____4333 =
              let uu____4334 =
                FStar_List.for_all
                  (fun uu____4342  ->
                     match uu____4342 with | (h,uu____4348) -> is_C h) args
                 in
              Prims.op_Negation uu____4334  in
            if uu____4333 then failwith "not a C (A * C)" else ()  in
          true
        else
          (let uu____4351 =
             let uu____4352 =
               let uu____4353 =
                 FStar_List.for_all
                   (fun uu____4362  ->
                      match uu____4362 with
                      | (h,uu____4368) ->
                          let uu____4369 = is_C h  in
                          Prims.op_Negation uu____4369) args
                  in
               Prims.op_Negation uu____4353  in
             if uu____4352 then failwith "not a C (C * A)" else ()  in
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4389 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____4389 with
         | M t1 ->
             let uu____4391 =
               let uu____4392 = is_C t1  in
               if uu____4392 then failwith "not a C (C -> C)" else ()  in
             true
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4396) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4402) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4408,uu____4409) -> is_C t1
    | uu____4450 -> false
  
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
          let uu____4481 =
            let uu____4482 =
              let uu____4497 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____4498 =
                let uu____4505 =
                  let uu____4510 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____4510)  in
                [uu____4505]  in
              (uu____4497, uu____4498)  in
            FStar_Syntax_Syntax.Tm_app uu____4482  in
          mk1 uu____4481  in
        let uu____4525 =
          let uu____4526 = FStar_Syntax_Syntax.mk_binder p  in [uu____4526]
           in
        FStar_Syntax_Util.abs uu____4525 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___70_4531  ->
    match uu___70_4531 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4532 -> false
  
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
        let return_if uu____4765 =
          match uu____4765 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4796 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4798 =
                       let uu____4799 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____4799  in
                     Prims.op_Negation uu____4798)
                   in
                if uu____4796
                then
                  let uu____4800 =
                    let uu____4805 =
                      let uu____4806 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____4807 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____4808 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4806 uu____4807 uu____4808
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4805)  in
                  FStar_Errors.raise_err uu____4800
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) ->
                   let uu____4818 = check1 t1 t2  in (rec_nm, s_e, u_e)
               | (M t1,M t2) ->
                   let uu____4821 = check1 t1 t2  in (rec_nm, s_e, u_e)
               | (N t1,M t2) ->
                   let uu____4824 = check1 t1 t2  in
                   let uu____4825 = mk_return env t1 s_e  in
                   ((M t1), uu____4825, u_e)
               | (M t1,N t2) ->
                   let uu____4828 =
                     let uu____4833 =
                       let uu____4834 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____4835 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____4836 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4834 uu____4835 uu____4836
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4833)
                      in
                   FStar_Errors.raise_err uu____4828)
           in
        let ensure_m env1 e2 =
          let strip_m uu___71_4883 =
            match uu___71_4883 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4899 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____4919 =
                let uu____4924 =
                  let uu____4925 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4925
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4924)  in
              FStar_Errors.raise_error uu____4919 e2.FStar_Syntax_Syntax.pos
          | M uu____4932 ->
              let uu____4933 = check env1 e2 context_nm  in
              strip_m uu____4933
           in
        let uu____4940 =
          let uu____4941 = FStar_Syntax_Subst.compress e  in
          uu____4941.FStar_Syntax_Syntax.n  in
        match uu____4940 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4950 ->
            let uu____4951 = infer env e  in return_if uu____4951
        | FStar_Syntax_Syntax.Tm_name uu____4958 ->
            let uu____4959 = infer env e  in return_if uu____4959
        | FStar_Syntax_Syntax.Tm_fvar uu____4966 ->
            let uu____4967 = infer env e  in return_if uu____4967
        | FStar_Syntax_Syntax.Tm_abs uu____4974 ->
            let uu____4991 = infer env e  in return_if uu____4991
        | FStar_Syntax_Syntax.Tm_constant uu____4998 ->
            let uu____4999 = infer env e  in return_if uu____4999
        | FStar_Syntax_Syntax.Tm_quoted uu____5006 ->
            let uu____5013 = infer env e  in return_if uu____5013
        | FStar_Syntax_Syntax.Tm_app uu____5020 ->
            let uu____5035 = infer env e  in return_if uu____5035
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5043 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____5043 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5105) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5111) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5117,uu____5118) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5159 ->
            let uu____5172 =
              let uu____5173 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5173  in
            failwith uu____5172
        | FStar_Syntax_Syntax.Tm_type uu____5180 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5187 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5206 ->
            let uu____5213 =
              let uu____5214 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5214  in
            failwith uu____5213
        | FStar_Syntax_Syntax.Tm_uvar uu____5221 ->
            let uu____5238 =
              let uu____5239 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5239  in
            failwith uu____5238
        | FStar_Syntax_Syntax.Tm_delayed uu____5246 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5277 =
              let uu____5278 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5278  in
            failwith uu____5277

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
      let uu____5306 =
        let uu____5307 = FStar_Syntax_Subst.compress e  in
        uu____5307.FStar_Syntax_Syntax.n  in
      match uu____5306 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5325 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____5325
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5372;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5373;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5379 =
                  let uu___86_5380 = rc  in
                  let uu____5381 =
                    let uu____5386 =
                      let uu____5387 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____5387  in
                    FStar_Pervasives_Native.Some uu____5386  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___86_5380.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5381;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___86_5380.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____5379
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___87_5397 = env  in
            let uu____5398 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____5398;
              subst = (uu___87_5397.subst);
              tc_const = (uu___87_5397.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____5418  ->
                 match uu____5418 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___88_5431 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___88_5431.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___88_5431.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____5432 =
            FStar_List.fold_left
              (fun uu____5461  ->
                 fun uu____5462  ->
                   match (uu____5461, uu____5462) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____5510 = is_C c  in
                       if uu____5510
                       then
                         let xw =
                           let uu____5518 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5518
                            in
                         let x =
                           let uu___89_5520 = bv  in
                           let uu____5521 =
                             let uu____5524 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____5524  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___89_5520.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___89_5520.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5521
                           }  in
                         let env3 =
                           let uu___90_5526 = env2  in
                           let uu____5527 =
                             let uu____5530 =
                               let uu____5531 =
                                 let uu____5538 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____5538)  in
                               FStar_Syntax_Syntax.NT uu____5531  in
                             uu____5530 :: (env2.subst)  in
                           {
                             env = (uu___90_5526.env);
                             subst = uu____5527;
                             tc_const = (uu___90_5526.tc_const)
                           }  in
                         let uu____5539 =
                           let uu____5542 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____5543 =
                             let uu____5546 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____5546 :: acc  in
                           uu____5542 :: uu____5543  in
                         (env3, uu____5539)
                       else
                         (let x =
                            let uu___91_5551 = bv  in
                            let uu____5552 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___91_5551.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___91_5551.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5552
                            }  in
                          let uu____5555 =
                            let uu____5558 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____5558 :: acc  in
                          (env2, uu____5555))) (env1, []) binders1
             in
          (match uu____5432 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____5578 =
                 let check_what =
                   let uu____5600 = is_monadic rc_opt1  in
                   if uu____5600 then check_m else check_n  in
                 let uu____5614 = check_what env2 body1  in
                 match uu____5614 with
                 | (t,s_body,u_body) ->
                     let uu____5630 =
                       let uu____5631 =
                         let uu____5632 = is_monadic rc_opt1  in
                         if uu____5632 then M t else N t  in
                       comp_of_nm uu____5631  in
                     (uu____5630, s_body, u_body)
                  in
               (match uu____5578 with
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
                                 let uu____5657 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___72_5661  ->
                                           match uu___72_5661 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5662 -> false))
                                    in
                                 if uu____5657
                                 then
                                   let uu____5663 =
                                     FStar_List.filter
                                       (fun uu___73_5667  ->
                                          match uu___73_5667 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5668 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5663
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5677 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___74_5681  ->
                                         match uu___74_5681 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5682 -> false))
                                  in
                               if uu____5677
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___75_5689  ->
                                        match uu___75_5689 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5690 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____5691 =
                                   let uu____5692 =
                                     let uu____5697 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____5697
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5692 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____5691
                               else
                                 (let uu____5699 =
                                    let uu___92_5700 = rc  in
                                    let uu____5701 =
                                      let uu____5706 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____5706
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___92_5700.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5701;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___92_5700.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____5699))
                       in
                    let uu____5707 =
                      let comp1 =
                        let uu____5717 = is_monadic rc_opt1  in
                        let uu____5718 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5717 uu____5718
                         in
                      let uu____5719 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____5719,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____5707 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____5761 =
                             let uu____5762 =
                               let uu____5779 =
                                 let uu____5782 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____5782 s_rc_opt  in
                               (s_binders1, s_body1, uu____5779)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5762  in
                           mk1 uu____5761  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____5792 =
                             let uu____5793 =
                               let uu____5810 =
                                 let uu____5813 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____5813 u_rc_opt  in
                               (u_binders2, u_body2, uu____5810)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5793  in
                           mk1 uu____5792  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5823;_};
            FStar_Syntax_Syntax.fv_delta = uu____5824;
            FStar_Syntax_Syntax.fv_qual = uu____5825;_}
          ->
          let uu____5828 =
            let uu____5833 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5833  in
          (match uu____5828 with
           | (uu____5864,t) ->
               let uu____5866 =
                 let uu____5867 = normalize1 t  in N uu____5867  in
               (uu____5866, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5868;
             FStar_Syntax_Syntax.vars = uu____5869;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5932 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5932 with
           | (unary_op,uu____5954) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6013;
             FStar_Syntax_Syntax.vars = uu____6014;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6090 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6090 with
           | (unary_op,uu____6112) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6177;
             FStar_Syntax_Syntax.vars = uu____6178;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____6216 = infer env a  in
          (match uu____6216 with
           | (t,s,u) ->
               let uu____6232 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6232 with
                | (head1,uu____6254) ->
                    let uu____6275 =
                      let uu____6276 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____6276  in
                    let uu____6277 =
                      let uu____6280 =
                        let uu____6281 =
                          let uu____6296 =
                            let uu____6299 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6299]  in
                          (head1, uu____6296)  in
                        FStar_Syntax_Syntax.Tm_app uu____6281  in
                      mk1 uu____6280  in
                    let uu____6304 =
                      let uu____6307 =
                        let uu____6308 =
                          let uu____6323 =
                            let uu____6326 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6326]  in
                          (head1, uu____6323)  in
                        FStar_Syntax_Syntax.Tm_app uu____6308  in
                      mk1 uu____6307  in
                    (uu____6275, uu____6277, uu____6304)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6335;
             FStar_Syntax_Syntax.vars = uu____6336;_},(a1,uu____6338)::a2::[])
          ->
          let uu____6380 = infer env a1  in
          (match uu____6380 with
           | (t,s,u) ->
               let uu____6396 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6396 with
                | (head1,uu____6418) ->
                    let uu____6439 =
                      let uu____6442 =
                        let uu____6443 =
                          let uu____6458 =
                            let uu____6461 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6461; a2]  in
                          (head1, uu____6458)  in
                        FStar_Syntax_Syntax.Tm_app uu____6443  in
                      mk1 uu____6442  in
                    let uu____6478 =
                      let uu____6481 =
                        let uu____6482 =
                          let uu____6497 =
                            let uu____6500 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6500; a2]  in
                          (head1, uu____6497)  in
                        FStar_Syntax_Syntax.Tm_app uu____6482  in
                      mk1 uu____6481  in
                    (t, uu____6439, uu____6478)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6521;
             FStar_Syntax_Syntax.vars = uu____6522;_},uu____6523)
          ->
          let uu____6544 =
            let uu____6549 =
              let uu____6550 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6550
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6549)  in
          FStar_Errors.raise_error uu____6544 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6557;
             FStar_Syntax_Syntax.vars = uu____6558;_},uu____6559)
          ->
          let uu____6580 =
            let uu____6585 =
              let uu____6586 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6586
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6585)  in
          FStar_Errors.raise_error uu____6580 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6615 = check_n env head1  in
          (match uu____6615 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6637 =
                   let uu____6638 = FStar_Syntax_Subst.compress t  in
                   uu____6638.FStar_Syntax_Syntax.n  in
                 match uu____6637 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6641 -> true
                 | uu____6654 -> false  in
               let rec flatten1 t =
                 let uu____6673 =
                   let uu____6674 = FStar_Syntax_Subst.compress t  in
                   uu____6674.FStar_Syntax_Syntax.n  in
                 match uu____6673 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6691);
                                FStar_Syntax_Syntax.pos = uu____6692;
                                FStar_Syntax_Syntax.vars = uu____6693;_})
                     when is_arrow t1 ->
                     let uu____6718 = flatten1 t1  in
                     (match uu____6718 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6800,uu____6801)
                     -> flatten1 e1
                 | uu____6842 ->
                     let uu____6843 =
                       let uu____6848 =
                         let uu____6849 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6849
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6848)  in
                     FStar_Errors.raise_err uu____6843
                  in
               let uu____6862 = flatten1 t_head  in
               (match uu____6862 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    let uu____6911 =
                      if
                        (FStar_List.length binders) <
                          (FStar_List.length args)
                      then
                        let uu____6922 =
                          let uu____6927 =
                            let uu____6928 = FStar_Util.string_of_int n1  in
                            let uu____6935 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____6946 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6928 uu____6935 uu____6946
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6927)
                           in
                        FStar_Errors.raise_err uu____6922
                      else ()  in
                    let uu____6954 =
                      FStar_Syntax_Subst.open_comp binders comp  in
                    (match uu____6954 with
                     | (binders1,comp1) ->
                         let rec final_type subst1 uu____7001 args1 =
                           match uu____7001 with
                           | (binders2,comp2) ->
                               (match (binders2, args1) with
                                | ([],[]) ->
                                    let uu____7075 =
                                      let uu____7076 =
                                        FStar_Syntax_Subst.subst_comp subst1
                                          comp2
                                         in
                                      uu____7076.FStar_Syntax_Syntax.n  in
                                    nm_of_comp uu____7075
                                | (binders3,[]) ->
                                    let uu____7106 =
                                      let uu____7107 =
                                        let uu____7110 =
                                          let uu____7111 =
                                            mk1
                                              (FStar_Syntax_Syntax.Tm_arrow
                                                 (binders3, comp2))
                                             in
                                          FStar_Syntax_Subst.subst subst1
                                            uu____7111
                                           in
                                        FStar_Syntax_Subst.compress
                                          uu____7110
                                         in
                                      uu____7107.FStar_Syntax_Syntax.n  in
                                    (match uu____7106 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (binders4,comp3) ->
                                         let uu____7136 =
                                           let uu____7137 =
                                             let uu____7138 =
                                               let uu____7151 =
                                                 FStar_Syntax_Subst.close_comp
                                                   binders4 comp3
                                                  in
                                               (binders4, uu____7151)  in
                                             FStar_Syntax_Syntax.Tm_arrow
                                               uu____7138
                                              in
                                           mk1 uu____7137  in
                                         N uu____7136
                                     | uu____7158 -> failwith "wat?")
                                | ([],uu____7159::uu____7160) ->
                                    failwith "just checked that?!"
                                | ((bv,uu____7200)::binders3,(arg,uu____7203)::args2)
                                    ->
                                    final_type
                                      ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                      subst1) (binders3, comp2) args2)
                            in
                         let final_type1 =
                           final_type [] (binders1, comp1) args  in
                         let uu____7256 = FStar_List.splitAt n' binders1  in
                         (match uu____7256 with
                          | (binders2,uu____7288) ->
                              let uu____7313 =
                                let uu____7334 =
                                  FStar_List.map2
                                    (fun uu____7388  ->
                                       fun uu____7389  ->
                                         match (uu____7388, uu____7389) with
                                         | ((bv,uu____7427),(arg,q)) ->
                                             let uu____7444 =
                                               let uu____7445 =
                                                 FStar_Syntax_Subst.compress
                                                   bv.FStar_Syntax_Syntax.sort
                                                  in
                                               uu____7445.FStar_Syntax_Syntax.n
                                                in
                                             (match uu____7444 with
                                              | FStar_Syntax_Syntax.Tm_type
                                                  uu____7464 ->
                                                  let uu____7465 =
                                                    let uu____7470 =
                                                      star_type' env arg  in
                                                    (uu____7470, q)  in
                                                  (uu____7465, [(arg, q)])
                                              | uu____7497 ->
                                                  let uu____7498 =
                                                    check_n env arg  in
                                                  (match uu____7498 with
                                                   | (uu____7521,s_arg,u_arg)
                                                       ->
                                                       let uu____7524 =
                                                         let uu____7531 =
                                                           is_C
                                                             bv.FStar_Syntax_Syntax.sort
                                                            in
                                                         if uu____7531
                                                         then
                                                           let uu____7538 =
                                                             let uu____7543 =
                                                               FStar_Syntax_Subst.subst
                                                                 env.subst
                                                                 s_arg
                                                                in
                                                             (uu____7543, q)
                                                              in
                                                           [uu____7538;
                                                           (u_arg, q)]
                                                         else [(u_arg, q)]
                                                          in
                                                       ((s_arg, q),
                                                         uu____7524))))
                                    binders2 args
                                   in
                                FStar_List.split uu____7334  in
                              (match uu____7313 with
                               | (s_args,u_args) ->
                                   let u_args1 = FStar_List.flatten u_args
                                      in
                                   let uu____7642 =
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_app
                                          (s_head, s_args))
                                      in
                                   let uu____7651 =
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_app
                                          (u_head, u_args1))
                                      in
                                   (final_type1, uu____7642, uu____7651))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7719) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7725) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7731,uu____7732) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7774 = let uu____7775 = env.tc_const c  in N uu____7775
             in
          (uu____7774, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7782 ->
          let uu____7795 =
            let uu____7796 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7796  in
          failwith uu____7795
      | FStar_Syntax_Syntax.Tm_type uu____7803 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7810 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7829 ->
          let uu____7836 =
            let uu____7837 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7837  in
          failwith uu____7836
      | FStar_Syntax_Syntax.Tm_uvar uu____7844 ->
          let uu____7861 =
            let uu____7862 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7862  in
          failwith uu____7861
      | FStar_Syntax_Syntax.Tm_delayed uu____7869 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7900 =
            let uu____7901 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7901  in
          failwith uu____7900

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
          let uu____7948 = check_n env e0  in
          match uu____7948 with
          | (uu____7961,s_e0,u_e0) ->
              let uu____7964 =
                let uu____7993 =
                  FStar_List.map
                    (fun b  ->
                       let uu____8054 = FStar_Syntax_Subst.open_branch b  in
                       match uu____8054 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___93_8096 = env  in
                             let uu____8097 =
                               let uu____8098 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____8098
                                in
                             {
                               env = uu____8097;
                               subst = (uu___93_8096.subst);
                               tc_const = (uu___93_8096.tc_const)
                             }  in
                           let uu____8101 = f env1 body  in
                           (match uu____8101 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8173 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____7993  in
              (match uu____7964 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____8275 = FStar_List.hd nms  in
                     match uu____8275 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___76_8281  ->
                          match uu___76_8281 with
                          | M uu____8282 -> true
                          | uu____8283 -> false) nms
                      in
                   let uu____8284 =
                     let uu____8321 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8411  ->
                              match uu____8411 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8588 =
                                         check env original_body (M t2)  in
                                       (match uu____8588 with
                                        | (uu____8625,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8664,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____8321  in
                   (match uu____8284 with
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
                              (fun uu____8848  ->
                                 match uu____8848 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8899 =
                                         let uu____8900 =
                                           let uu____8915 =
                                             let uu____8922 =
                                               let uu____8927 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____8928 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____8927, uu____8928)  in
                                             [uu____8922]  in
                                           (s_body, uu____8915)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8900
                                          in
                                       mk1 uu____8899  in
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
                            let uu____8960 =
                              let uu____8961 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____8961]  in
                            let uu____8962 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____8960 uu____8962
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____8968 =
                              let uu____8975 =
                                let uu____8976 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8976
                                 in
                              [uu____8975]  in
                            let uu____8977 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____8968 uu____8977  in
                          let uu____8980 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____9019 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____8980, uu____9019)
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
                           let uu____9036 =
                             let uu____9039 =
                               let uu____9040 =
                                 let uu____9067 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____9067,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____9040  in
                             mk1 uu____9039  in
                           let uu____9104 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____9036, uu____9104))))

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
              let uu____9153 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____9153]  in
            let uu____9154 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____9154 with
            | (x_binders1,e21) ->
                let uu____9167 = infer env e1  in
                (match uu____9167 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____9184 = is_C t1  in
                       if uu____9184
                       then
                         let uu___94_9185 = binding  in
                         let uu____9186 =
                           let uu____9189 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____9189  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___94_9185.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_9185.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9186;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_9185.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___94_9185.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___94_9185.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___94_9185.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___95_9192 = env  in
                       let uu____9193 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___96_9195 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___96_9195.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___96_9195.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9193;
                         subst = (uu___95_9192.subst);
                         tc_const = (uu___95_9192.tc_const)
                       }  in
                     let uu____9196 = proceed env1 e21  in
                     (match uu____9196 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___97_9213 = binding  in
                            let uu____9214 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___97_9213.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___97_9213.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9214;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___97_9213.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___97_9213.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___97_9213.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___97_9213.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____9217 =
                            let uu____9220 =
                              let uu____9221 =
                                let uu____9234 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___98_9244 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___98_9244.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___98_9244.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___98_9244.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___98_9244.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___98_9244.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___98_9244.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9234)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9221  in
                            mk1 uu____9220  in
                          let uu____9245 =
                            let uu____9248 =
                              let uu____9249 =
                                let uu____9262 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___99_9272 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___99_9272.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___99_9272.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___99_9272.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___99_9272.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___99_9272.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___99_9272.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9262)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9249  in
                            mk1 uu____9248  in
                          (nm_rec, uu____9217, uu____9245))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___100_9281 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___100_9281.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___100_9281.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___100_9281.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___100_9281.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___100_9281.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___101_9283 = env  in
                       let uu____9284 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___102_9286 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___102_9286.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___102_9286.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9284;
                         subst = (uu___101_9283.subst);
                         tc_const = (uu___101_9283.tc_const)
                       }  in
                     let uu____9287 = ensure_m env1 e21  in
                     (match uu____9287 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____9310 =
                              let uu____9311 =
                                let uu____9326 =
                                  let uu____9333 =
                                    let uu____9338 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____9339 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9338, uu____9339)  in
                                  [uu____9333]  in
                                (s_e2, uu____9326)  in
                              FStar_Syntax_Syntax.Tm_app uu____9311  in
                            mk1 uu____9310  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____9358 =
                              let uu____9359 =
                                let uu____9374 =
                                  let uu____9381 =
                                    let uu____9386 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____9386)  in
                                  [uu____9381]  in
                                (s_e1, uu____9374)  in
                              FStar_Syntax_Syntax.Tm_app uu____9359  in
                            mk1 uu____9358  in
                          let uu____9401 =
                            let uu____9402 =
                              let uu____9403 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____9403]  in
                            FStar_Syntax_Util.abs uu____9402 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____9404 =
                            let uu____9407 =
                              let uu____9408 =
                                let uu____9421 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___103_9431 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___103_9431.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___103_9431.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___103_9431.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___103_9431.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___103_9431.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___103_9431.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9421)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9408  in
                            mk1 uu____9407  in
                          ((M t2), uu____9401, uu____9404)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9443 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____9443  in
      let uu____9444 = check env e mn  in
      match uu____9444 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9460 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9482 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____9482  in
      let uu____9483 = check env e mn  in
      match uu____9483 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9499 -> failwith "[check_m]: impossible"

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
        let uu____9528 =
          let uu____9529 =
            let uu____9530 = is_C c  in Prims.op_Negation uu____9530  in
          if uu____9529 then failwith "not a C" else ()  in
        let mk1 x =
          FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
            c.FStar_Syntax_Syntax.pos
           in
        let uu____9540 =
          let uu____9541 = FStar_Syntax_Subst.compress c  in
          uu____9541.FStar_Syntax_Syntax.n  in
        match uu____9540 with
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let uu____9566 = FStar_Syntax_Util.head_and_args wp  in
            (match uu____9566 with
             | (wp_head,wp_args) ->
                 let uu____9603 =
                   let uu____9604 =
                     (Prims.op_Negation
                        ((FStar_List.length wp_args) =
                           (FStar_List.length args)))
                       ||
                       (let uu____9618 =
                          let uu____9619 =
                            FStar_Parser_Const.mk_tuple_data_lid
                              (FStar_List.length wp_args)
                              FStar_Range.dummyRange
                             in
                          FStar_Syntax_Util.is_constructor wp_head uu____9619
                           in
                        Prims.op_Negation uu____9618)
                      in
                   if uu____9604 then failwith "mismatch" else ()  in
                 let uu____9627 =
                   let uu____9628 =
                     let uu____9643 =
                       FStar_List.map2
                         (fun uu____9671  ->
                            fun uu____9672  ->
                              match (uu____9671, uu____9672) with
                              | ((arg,q),(wp_arg,q')) ->
                                  let print_implicit q1 =
                                    let uu____9711 =
                                      FStar_Syntax_Syntax.is_implicit q1  in
                                    if uu____9711
                                    then "implicit"
                                    else "explicit"  in
                                  let uu____9713 =
                                    if q <> q'
                                    then
                                      let uu____9714 =
                                        let uu____9719 =
                                          let uu____9720 = print_implicit q
                                             in
                                          let uu____9721 = print_implicit q'
                                             in
                                          FStar_Util.format2
                                            "Incoherent implicit qualifiers %b %b\n"
                                            uu____9720 uu____9721
                                           in
                                        (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                          uu____9719)
                                         in
                                      FStar_Errors.log_issue
                                        head1.FStar_Syntax_Syntax.pos
                                        uu____9714
                                    else ()  in
                                  let uu____9723 = trans_F_ env arg wp_arg
                                     in
                                  (uu____9723, q)) args wp_args
                        in
                     (head1, uu____9643)  in
                   FStar_Syntax_Syntax.Tm_app uu____9628  in
                 mk1 uu____9627)
        | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
            let binders1 = FStar_Syntax_Util.name_binders binders  in
            let uu____9757 = FStar_Syntax_Subst.open_comp binders1 comp  in
            (match uu____9757 with
             | (binders_orig,comp1) ->
                 let uu____9764 =
                   let uu____9779 =
                     FStar_List.map
                       (fun uu____9813  ->
                          match uu____9813 with
                          | (bv,q) ->
                              let h = bv.FStar_Syntax_Syntax.sort  in
                              let uu____9833 = is_C h  in
                              if uu____9833
                              then
                                let w' =
                                  let uu____9845 = star_type' env h  in
                                  FStar_Syntax_Syntax.gen_bv
                                    (Prims.strcat
                                       (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                       "__w'") FStar_Pervasives_Native.None
                                    uu____9845
                                   in
                                let uu____9846 =
                                  let uu____9853 =
                                    let uu____9860 =
                                      let uu____9865 =
                                        let uu____9866 =
                                          let uu____9867 =
                                            FStar_Syntax_Syntax.bv_to_name w'
                                             in
                                          trans_F_ env h uu____9867  in
                                        FStar_Syntax_Syntax.null_bv
                                          uu____9866
                                         in
                                      (uu____9865, q)  in
                                    [uu____9860]  in
                                  (w', q) :: uu____9853  in
                                (w', uu____9846)
                              else
                                (let x =
                                   let uu____9888 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__x") FStar_Pervasives_Native.None
                                     uu____9888
                                    in
                                 (x, [(x, q)]))) binders_orig
                      in
                   FStar_List.split uu____9779  in
                 (match uu____9764 with
                  | (bvs,binders2) ->
                      let binders3 = FStar_List.flatten binders2  in
                      let comp2 =
                        let uu____9943 =
                          let uu____9946 =
                            FStar_Syntax_Syntax.binders_of_list bvs  in
                          FStar_Syntax_Util.rename_binders binders_orig
                            uu____9946
                           in
                        FStar_Syntax_Subst.subst_comp uu____9943 comp1  in
                      let app =
                        let uu____9950 =
                          let uu____9951 =
                            let uu____9966 =
                              FStar_List.map
                                (fun bv  ->
                                   let uu____9981 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   let uu____9982 =
                                     FStar_Syntax_Syntax.as_implicit false
                                      in
                                   (uu____9981, uu____9982)) bvs
                               in
                            (wp, uu____9966)  in
                          FStar_Syntax_Syntax.Tm_app uu____9951  in
                        mk1 uu____9950  in
                      let comp3 =
                        let uu____9990 = type_of_comp comp2  in
                        let uu____9991 = is_monadic_comp comp2  in
                        trans_G env uu____9990 uu____9991 app  in
                      FStar_Syntax_Util.arrow binders3 comp3))
        | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9993,uu____9994) ->
            trans_F_ env e wp
        | uu____10035 -> failwith "impossible trans_F_"

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
            let uu____10040 =
              let uu____10041 = star_type' env h  in
              let uu____10044 =
                let uu____10053 =
                  let uu____10058 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____10058)  in
                [uu____10053]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____10041;
                FStar_Syntax_Syntax.effect_args = uu____10044;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____10040
          else
            (let uu____10068 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____10068)

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
    fun t  -> let uu____10087 = n env.env t  in star_type' env uu____10087
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____10106 = n env.env t  in check_n env uu____10106
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____10122 = n env.env c  in
        let uu____10123 = n env.env wp  in
        trans_F_ env uu____10122 uu____10123
  