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
            (let uu____130 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____130
             then
               (d "Elaborating extra WP combinators";
                (let uu____132 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____132))
             else ());
            (let rec collect_binders t =
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
                     | uu____190 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____193 = collect_binders rest  in
                   FStar_List.append bs uu____193
               | FStar_Syntax_Syntax.Tm_type uu____204 -> []
               | uu____209 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____229 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____229 FStar_Syntax_Util.name_binders
                in
             (let uu____249 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____249
              then
                let uu____250 =
                  let uu____251 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____251  in
                d uu____250
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____285 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____285 with
                | (sigelt,fv) ->
                    ((let uu____293 =
                        let uu____296 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____296
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____293);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____426  ->
                     match uu____426 with
                     | (t,b) ->
                         let uu____437 = FStar_Syntax_Syntax.as_implicit b
                            in
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
                      let uu____537 =
                        let uu____540 = FStar_Syntax_Syntax.bv_to_name t  in
                        f uu____540  in
                      FStar_Syntax_Util.arrow gamma uu____537  in
                    let uu____541 =
                      let uu____542 =
                        let uu____549 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____550 =
                          let uu____553 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____553]  in
                        uu____549 :: uu____550  in
                      FStar_List.append binders uu____542  in
                    FStar_Syntax_Util.abs uu____541 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____558 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____559 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____558, uu____559)  in
                match uu____513 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____599 =
                        let uu____600 =
                          let uu____615 =
                            let uu____622 =
                              FStar_List.map
                                (fun uu____642  ->
                                   match uu____642 with
                                   | (bv,uu____652) ->
                                       let uu____653 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____654 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____653, uu____654)) binders
                               in
                            let uu____655 =
                              let uu____662 =
                                let uu____667 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____668 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____667, uu____668)  in
                              let uu____669 =
                                let uu____676 =
                                  let uu____681 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____681)  in
                                [uu____676]  in
                              uu____662 :: uu____669  in
                            FStar_List.append uu____622 uu____655  in
                          (fv, uu____615)  in
                        FStar_Syntax_Syntax.Tm_app uu____600  in
                      mk1 uu____599  in
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
                      let uu____746 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____746
                       in
                    let ret1 =
                      let uu____750 =
                        let uu____751 =
                          let uu____754 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____754  in
                        FStar_Syntax_Util.residual_tot uu____751  in
                      FStar_Pervasives_Native.Some uu____750  in
                    let body =
                      let uu____756 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____756 ret1  in
                    let uu____757 =
                      let uu____758 = mk_all_implicit binders  in
                      let uu____765 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____758 uu____765  in
                    FStar_Syntax_Util.abs uu____757 body ret1  in
                  let c_pure1 =
                    let uu____793 = mk_lid "pure"  in
                    register env1 uu____793 c_pure  in
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
                      let uu____798 =
                        let uu____799 =
                          let uu____800 =
                            let uu____807 =
                              let uu____808 =
                                let uu____809 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____809
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____808  in
                            [uu____807]  in
                          let uu____810 =
                            let uu____813 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____813  in
                          FStar_Syntax_Util.arrow uu____800 uu____810  in
                        mk_gctx uu____799  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____798
                       in
                    let r =
                      let uu____815 =
                        let uu____816 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____816  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____815
                       in
                    let ret1 =
                      let uu____820 =
                        let uu____821 =
                          let uu____824 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____824  in
                        FStar_Syntax_Util.residual_tot uu____821  in
                      FStar_Pervasives_Native.Some uu____820  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____832 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____835 =
                          let uu____844 =
                            let uu____847 =
                              let uu____848 =
                                let uu____849 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____849
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____848  in
                            [uu____847]  in
                          FStar_List.append gamma_as_args uu____844  in
                        FStar_Syntax_Util.mk_app uu____832 uu____835  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____852 =
                      let uu____853 = mk_all_implicit binders  in
                      let uu____860 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____853 uu____860  in
                    FStar_Syntax_Util.abs uu____852 outer_body ret1  in
                  let c_app1 =
                    let uu____896 = mk_lid "app"  in
                    register env1 uu____896 c_app  in
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
                      let uu____903 =
                        let uu____910 =
                          let uu____911 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____911  in
                        [uu____910]  in
                      let uu____912 =
                        let uu____915 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____915  in
                      FStar_Syntax_Util.arrow uu____903 uu____912  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____918 =
                        let uu____919 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____919  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____918
                       in
                    let ret1 =
                      let uu____923 =
                        let uu____924 =
                          let uu____927 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____927  in
                        FStar_Syntax_Util.residual_tot uu____924  in
                      FStar_Pervasives_Native.Some uu____923  in
                    let uu____928 =
                      let uu____929 = mk_all_implicit binders  in
                      let uu____936 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____929 uu____936  in
                    let uu____971 =
                      let uu____972 =
                        let uu____981 =
                          let uu____984 =
                            let uu____987 =
                              let uu____996 =
                                let uu____999 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____999]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____996
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____987  in
                          let uu____1000 =
                            let uu____1005 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1005]  in
                          uu____984 :: uu____1000  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____981
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____972  in
                    FStar_Syntax_Util.abs uu____928 uu____971 ret1  in
                  let c_lift11 =
                    let uu____1009 = mk_lid "lift1"  in
                    register env1 uu____1009 c_lift1  in
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
                      let uu____1017 =
                        let uu____1024 =
                          let uu____1025 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1025  in
                        let uu____1026 =
                          let uu____1029 =
                            let uu____1030 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1030  in
                          [uu____1029]  in
                        uu____1024 :: uu____1026  in
                      let uu____1031 =
                        let uu____1034 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1034  in
                      FStar_Syntax_Util.arrow uu____1017 uu____1031  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1037 =
                        let uu____1038 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1038  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1037
                       in
                    let a2 =
                      let uu____1040 =
                        let uu____1041 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1041  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1040
                       in
                    let ret1 =
                      let uu____1045 =
                        let uu____1046 =
                          let uu____1049 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1049  in
                        FStar_Syntax_Util.residual_tot uu____1046  in
                      FStar_Pervasives_Native.Some uu____1045  in
                    let uu____1050 =
                      let uu____1051 = mk_all_implicit binders  in
                      let uu____1058 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1051 uu____1058  in
                    let uu____1101 =
                      let uu____1102 =
                        let uu____1111 =
                          let uu____1114 =
                            let uu____1117 =
                              let uu____1126 =
                                let uu____1129 =
                                  let uu____1132 =
                                    let uu____1141 =
                                      let uu____1144 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1144]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1141
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1132
                                   in
                                let uu____1145 =
                                  let uu____1150 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1150]  in
                                uu____1129 :: uu____1145  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1126
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1117  in
                          let uu____1153 =
                            let uu____1158 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1158]  in
                          uu____1114 :: uu____1153  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1111
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1102  in
                    FStar_Syntax_Util.abs uu____1050 uu____1101 ret1  in
                  let c_lift21 =
                    let uu____1162 = mk_lid "lift2"  in
                    register env1 uu____1162 c_lift2  in
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
                      let uu____1169 =
                        let uu____1176 =
                          let uu____1177 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1177  in
                        [uu____1176]  in
                      let uu____1178 =
                        let uu____1181 =
                          let uu____1182 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1182  in
                        FStar_Syntax_Syntax.mk_Total uu____1181  in
                      FStar_Syntax_Util.arrow uu____1169 uu____1178  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1187 =
                        let uu____1188 =
                          let uu____1191 =
                            let uu____1192 =
                              let uu____1199 =
                                let uu____1200 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1200
                                 in
                              [uu____1199]  in
                            let uu____1201 =
                              let uu____1204 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1204  in
                            FStar_Syntax_Util.arrow uu____1192 uu____1201  in
                          mk_ctx uu____1191  in
                        FStar_Syntax_Util.residual_tot uu____1188  in
                      FStar_Pervasives_Native.Some uu____1187  in
                    let e1 =
                      let uu____1206 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1206
                       in
                    let body =
                      let uu____1208 =
                        let uu____1209 =
                          let uu____1216 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1216]  in
                        FStar_List.append gamma uu____1209  in
                      let uu____1221 =
                        let uu____1222 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1225 =
                          let uu____1234 =
                            let uu____1235 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1235  in
                          let uu____1236 = args_of_binders1 gamma  in
                          uu____1234 :: uu____1236  in
                        FStar_Syntax_Util.mk_app uu____1222 uu____1225  in
                      FStar_Syntax_Util.abs uu____1208 uu____1221 ret1  in
                    let uu____1239 =
                      let uu____1240 = mk_all_implicit binders  in
                      let uu____1247 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1240 uu____1247  in
                    FStar_Syntax_Util.abs uu____1239 body ret1  in
                  let c_push1 =
                    let uu____1279 = mk_lid "push"  in
                    register env1 uu____1279 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1301 =
                        let uu____1302 =
                          let uu____1317 = args_of_binders1 binders  in
                          (c, uu____1317)  in
                        FStar_Syntax_Syntax.Tm_app uu____1302  in
                      mk1 uu____1301
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1327 =
                        let uu____1328 =
                          let uu____1335 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1336 =
                            let uu____1339 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1339]  in
                          uu____1335 :: uu____1336  in
                        let uu____1340 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1328 uu____1340  in
                      FStar_Syntax_Syntax.mk_Total uu____1327  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1344 =
                      let uu____1345 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1345  in
                    let uu____1356 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1358 =
                        let uu____1361 =
                          let uu____1370 =
                            let uu____1373 =
                              let uu____1376 =
                                let uu____1385 =
                                  let uu____1386 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1386  in
                                [uu____1385]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1376  in
                            [uu____1373]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1370
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1361  in
                      FStar_Syntax_Util.ascribe uu____1358
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1344 uu____1356
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1406 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1406 wp_if_then_else  in
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
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1417 =
                        let uu____1426 =
                          let uu____1429 =
                            let uu____1432 =
                              let uu____1441 =
                                let uu____1444 =
                                  let uu____1447 =
                                    let uu____1456 =
                                      let uu____1457 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1457
                                       in
                                    [uu____1456]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1447
                                   in
                                [uu____1444]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1441
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1432  in
                          let uu____1462 =
                            let uu____1467 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1467]  in
                          uu____1429 :: uu____1462  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1426
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1417  in
                    let uu____1470 =
                      let uu____1471 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1471  in
                    FStar_Syntax_Util.abs uu____1470 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1483 = mk_lid "wp_assert"  in
                    register env1 uu____1483 wp_assert  in
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
                           (Prims.parse_int "1"))
                        FStar_Pervasives_Native.None
                       in
                    let body =
                      let uu____1494 =
                        let uu____1503 =
                          let uu____1506 =
                            let uu____1509 =
                              let uu____1518 =
                                let uu____1521 =
                                  let uu____1524 =
                                    let uu____1533 =
                                      let uu____1534 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1534
                                       in
                                    [uu____1533]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1524
                                   in
                                [uu____1521]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1518
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1509  in
                          let uu____1539 =
                            let uu____1544 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1544]  in
                          uu____1506 :: uu____1539  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1503
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1494  in
                    let uu____1547 =
                      let uu____1548 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1548  in
                    FStar_Syntax_Util.abs uu____1547 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1560 = mk_lid "wp_assume"  in
                    register env1 uu____1560 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1569 =
                        let uu____1576 =
                          let uu____1577 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1577  in
                        [uu____1576]  in
                      let uu____1578 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1569 uu____1578  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1585 =
                        let uu____1594 =
                          let uu____1597 =
                            let uu____1600 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1600  in
                          let uu____1609 =
                            let uu____1614 =
                              let uu____1617 =
                                let uu____1626 =
                                  let uu____1629 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1629]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1626
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1617  in
                            [uu____1614]  in
                          uu____1597 :: uu____1609  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1594
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1585  in
                    let uu____1636 =
                      let uu____1637 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1637  in
                    FStar_Syntax_Util.abs uu____1636 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1649 = mk_lid "wp_close"  in
                    register env1 uu____1649 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____1659 =
                      let uu____1660 =
                        let uu____1661 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1661
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1660  in
                    FStar_Pervasives_Native.Some uu____1659  in
                  let mk_forall1 x body =
                    let uu____1677 =
                      let uu____1684 =
                        let uu____1685 =
                          let uu____1700 =
                            let uu____1703 =
                              let uu____1704 =
                                let uu____1705 =
                                  let uu____1706 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1706]  in
                                FStar_Syntax_Util.abs uu____1705 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1704  in
                            [uu____1703]  in
                          (FStar_Syntax_Util.tforall, uu____1700)  in
                        FStar_Syntax_Syntax.Tm_app uu____1685  in
                      FStar_Syntax_Syntax.mk uu____1684  in
                    uu____1677 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____1718 =
                      let uu____1719 = FStar_Syntax_Subst.compress t  in
                      uu____1719.FStar_Syntax_Syntax.n  in
                    match uu____1718 with
                    | FStar_Syntax_Syntax.Tm_type uu____1722 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1748  ->
                              match uu____1748 with
                              | (b,uu____1754) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1755 -> true  in
                  let rec is_monotonic t =
                    let uu____1762 =
                      let uu____1763 = FStar_Syntax_Subst.compress t  in
                      uu____1763.FStar_Syntax_Syntax.n  in
                    match uu____1762 with
                    | FStar_Syntax_Syntax.Tm_type uu____1766 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1792  ->
                              match uu____1792 with
                              | (b,uu____1798) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1799 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____1865 =
                      let uu____1866 = FStar_Syntax_Subst.compress t1  in
                      uu____1866.FStar_Syntax_Syntax.n  in
                    match uu____1865 with
                    | FStar_Syntax_Syntax.Tm_type uu____1869 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1872);
                                      FStar_Syntax_Syntax.pos = uu____1873;
                                      FStar_Syntax_Syntax.vars = uu____1874;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1908 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1908
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____1911 =
                              let uu____1914 =
                                let uu____1923 =
                                  let uu____1924 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1924  in
                                [uu____1923]  in
                              FStar_Syntax_Util.mk_app x uu____1914  in
                            let uu____1925 =
                              let uu____1928 =
                                let uu____1937 =
                                  let uu____1938 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1938  in
                                [uu____1937]  in
                              FStar_Syntax_Util.mk_app y uu____1928  in
                            mk_rel1 b uu____1911 uu____1925  in
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
                             let uu____1943 =
                               let uu____1944 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1947 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1944 uu____1947  in
                             let uu____1950 =
                               let uu____1951 =
                                 let uu____1954 =
                                   let uu____1963 =
                                     let uu____1964 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1964
                                      in
                                   [uu____1963]  in
                                 FStar_Syntax_Util.mk_app x uu____1954  in
                               let uu____1965 =
                                 let uu____1968 =
                                   let uu____1977 =
                                     let uu____1978 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1978
                                      in
                                   [uu____1977]  in
                                 FStar_Syntax_Util.mk_app y uu____1968  in
                               mk_rel1 b uu____1951 uu____1965  in
                             FStar_Syntax_Util.mk_imp uu____1943 uu____1950
                              in
                           let uu____1979 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1979)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1982);
                                      FStar_Syntax_Syntax.pos = uu____1983;
                                      FStar_Syntax_Syntax.vars = uu____1984;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2018 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2018
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2021 =
                              let uu____2024 =
                                let uu____2033 =
                                  let uu____2034 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2034  in
                                [uu____2033]  in
                              FStar_Syntax_Util.mk_app x uu____2024  in
                            let uu____2035 =
                              let uu____2038 =
                                let uu____2047 =
                                  let uu____2048 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2048  in
                                [uu____2047]  in
                              FStar_Syntax_Util.mk_app y uu____2038  in
                            mk_rel1 b uu____2021 uu____2035  in
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
                             let uu____2053 =
                               let uu____2054 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2057 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2054 uu____2057  in
                             let uu____2060 =
                               let uu____2061 =
                                 let uu____2064 =
                                   let uu____2073 =
                                     let uu____2074 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2074
                                      in
                                   [uu____2073]  in
                                 FStar_Syntax_Util.mk_app x uu____2064  in
                               let uu____2075 =
                                 let uu____2078 =
                                   let uu____2087 =
                                     let uu____2088 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2088
                                      in
                                   [uu____2087]  in
                                 FStar_Syntax_Util.mk_app y uu____2078  in
                               mk_rel1 b uu____2061 uu____2075  in
                             FStar_Syntax_Util.mk_imp uu____2053 uu____2060
                              in
                           let uu____2089 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2089)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___78_2120 = t1  in
                          let uu____2121 =
                            let uu____2122 =
                              let uu____2135 =
                                let uu____2136 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2136  in
                              ([binder], uu____2135)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2122  in
                          {
                            FStar_Syntax_Syntax.n = uu____2121;
                            FStar_Syntax_Syntax.pos =
                              (uu___78_2120.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___78_2120.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2151 ->
                        failwith "unhandled arrow"
                    | uu____2164 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____2185 =
                        let uu____2186 = FStar_Syntax_Subst.compress t1  in
                        uu____2186.FStar_Syntax_Syntax.n  in
                      match uu____2185 with
                      | FStar_Syntax_Syntax.Tm_type uu____2189 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2212 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____2212
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2231 =
                                let uu____2232 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2232 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2231
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2259 =
                            let uu____2266 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2280  ->
                                     match uu____2280 with
                                     | (t2,q) ->
                                         let uu____2287 = project i x  in
                                         let uu____2288 = project i y  in
                                         mk_stronger t2 uu____2287 uu____2288)
                                args
                               in
                            match uu____2266 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2259 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2315);
                                      FStar_Syntax_Syntax.pos = uu____2316;
                                      FStar_Syntax_Syntax.vars = uu____2317;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2355  ->
                                   match uu____2355 with
                                   | (bv,q) ->
                                       let uu____2362 =
                                         let uu____2363 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2363  in
                                       FStar_Syntax_Syntax.gen_bv uu____2362
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2370 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2370) bvs
                             in
                          let body =
                            let uu____2372 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2373 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2372 uu____2373  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2380);
                                      FStar_Syntax_Syntax.pos = uu____2381;
                                      FStar_Syntax_Syntax.vars = uu____2382;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2420  ->
                                   match uu____2420 with
                                   | (bv,q) ->
                                       let uu____2427 =
                                         let uu____2428 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2428  in
                                       FStar_Syntax_Syntax.gen_bv uu____2427
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2435 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2435) bvs
                             in
                          let body =
                            let uu____2437 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2438 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2437 uu____2438  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2443 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____2445 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____2446 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____2447 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____2445 uu____2446 uu____2447  in
                    let uu____2448 =
                      let uu____2449 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____2449  in
                    FStar_Syntax_Util.abs uu____2448 body ret_tot_type  in
                  let stronger1 =
                    let uu____2477 = mk_lid "stronger"  in
                    register env1 uu____2477 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2483 = FStar_Util.prefix gamma  in
                    match uu____2483 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____2528 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2528
                             in
                          let uu____2531 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____2531 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2541 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____2541  in
                              let guard_free1 =
                                let uu____2551 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____2551  in
                              let pat =
                                let uu____2555 =
                                  let uu____2564 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____2564]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2555
                                 in
                              let pattern_guarded_body =
                                let uu____2568 =
                                  let uu____2569 =
                                    let uu____2576 =
                                      let uu____2577 =
                                        let uu____2588 =
                                          let uu____2591 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____2591]  in
                                        [uu____2588]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2577
                                       in
                                    (body, uu____2576)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____2569  in
                                mk1 uu____2568  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2596 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____2600 =
                            let uu____2601 =
                              let uu____2602 =
                                let uu____2603 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____2606 =
                                  let uu____2615 = args_of_binders1 wp_args
                                     in
                                  let uu____2618 =
                                    let uu____2621 =
                                      let uu____2622 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____2622
                                       in
                                    [uu____2621]  in
                                  FStar_List.append uu____2615 uu____2618  in
                                FStar_Syntax_Util.mk_app uu____2603
                                  uu____2606
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2602  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2601
                             in
                          FStar_Syntax_Util.abs gamma uu____2600
                            ret_gtot_type
                           in
                        let uu____2623 =
                          let uu____2624 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____2624  in
                        FStar_Syntax_Util.abs uu____2623 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____2636 = mk_lid "wp_ite"  in
                    register env1 uu____2636 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2642 = FStar_Util.prefix gamma  in
                    match uu____2642 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____2685 =
                            let uu____2686 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____2689 =
                              let uu____2698 =
                                let uu____2699 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____2699  in
                              [uu____2698]  in
                            FStar_Syntax_Util.mk_app uu____2686 uu____2689
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2685
                           in
                        let uu____2700 =
                          let uu____2701 =
                            let uu____2708 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____2708 gamma  in
                          FStar_List.append binders uu____2701  in
                        FStar_Syntax_Util.abs uu____2700 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____2724 = mk_lid "null_wp"  in
                    register env1 uu____2724 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____2733 =
                        let uu____2742 =
                          let uu____2745 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____2746 =
                            let uu____2749 =
                              let uu____2752 =
                                let uu____2761 =
                                  let uu____2762 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____2762  in
                                [uu____2761]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2752
                               in
                            let uu____2763 =
                              let uu____2768 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____2768]  in
                            uu____2749 :: uu____2763  in
                          uu____2745 :: uu____2746  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2742
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____2733  in
                    let uu____2771 =
                      let uu____2772 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____2772  in
                    FStar_Syntax_Util.abs uu____2771 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____2784 = mk_lid "wp_trivial"  in
                    register env1 uu____2784 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____2789 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____2789
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____2796 =
                      let uu____2799 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____2799  in
                    let uu____2851 =
                      let uu___79_2852 = ed  in
                      let uu____2853 =
                        let uu____2854 = c wp_if_then_else2  in
                        ([], uu____2854)  in
                      let uu____2857 =
                        let uu____2858 = c wp_ite2  in ([], uu____2858)  in
                      let uu____2861 =
                        let uu____2862 = c stronger2  in ([], uu____2862)  in
                      let uu____2865 =
                        let uu____2866 = c wp_close2  in ([], uu____2866)  in
                      let uu____2869 =
                        let uu____2870 = c wp_assert2  in ([], uu____2870)
                         in
                      let uu____2873 =
                        let uu____2874 = c wp_assume2  in ([], uu____2874)
                         in
                      let uu____2877 =
                        let uu____2878 = c null_wp2  in ([], uu____2878)  in
                      let uu____2881 =
                        let uu____2882 = c wp_trivial2  in ([], uu____2882)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___79_2852.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___79_2852.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___79_2852.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___79_2852.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___79_2852.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___79_2852.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___79_2852.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2853;
                        FStar_Syntax_Syntax.ite_wp = uu____2857;
                        FStar_Syntax_Syntax.stronger = uu____2861;
                        FStar_Syntax_Syntax.close_wp = uu____2865;
                        FStar_Syntax_Syntax.assert_p = uu____2869;
                        FStar_Syntax_Syntax.assume_p = uu____2873;
                        FStar_Syntax_Syntax.null_wp = uu____2877;
                        FStar_Syntax_Syntax.trivial = uu____2881;
                        FStar_Syntax_Syntax.repr =
                          (uu___79_2852.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___79_2852.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___79_2852.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___79_2852.FStar_Syntax_Syntax.actions);
                        FStar_Syntax_Syntax.eff_attrs =
                          (uu___79_2852.FStar_Syntax_Syntax.eff_attrs)
                      }  in
                    (uu____2796, uu____2851)))))
  
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___80_2902 = dmff_env  in
      {
        env = env';
        subst = (uu___80_2902.subst);
        tc_const = (uu___80_2902.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____2917 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____2931 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___66_2943  ->
    match uu___66_2943 with
    | FStar_Syntax_Syntax.Total (t,uu____2945) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___65_2958  ->
                match uu___65_2958 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2959 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2961 =
          let uu____2962 =
            let uu____2963 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2963
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2962  in
        failwith uu____2961
    | FStar_Syntax_Syntax.GTotal uu____2964 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___67_2977  ->
    match uu___67_2977 with
    | N t ->
        let uu____2979 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2979
    | M t ->
        let uu____2981 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2981
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2987,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2989;
                      FStar_Syntax_Syntax.vars = uu____2990;_})
        -> nm_of_comp n2
    | uu____3007 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____3017 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____3017 with | M uu____3018 -> true | N uu____3019 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3025 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____3039 =
        let uu____3046 =
          let uu____3047 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3047  in
        [uu____3046]  in
      let uu____3048 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3039 uu____3048  in
    let uu____3051 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3051
  
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
        let uu____3096 =
          let uu____3097 =
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
          FStar_Syntax_Syntax.Tm_arrow uu____3097  in
        mk1 uu____3096

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3167) ->
          let binders1 =
            FStar_List.map
              (fun uu____3203  ->
                 match uu____3203 with
                 | (bv,aqual) ->
                     let uu____3214 =
                       let uu___81_3215 = bv  in
                       let uu____3216 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___81_3215.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___81_3215.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3216
                       }  in
                     (uu____3214, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3219,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3221);
                             FStar_Syntax_Syntax.pos = uu____3222;
                             FStar_Syntax_Syntax.vars = uu____3223;_})
               ->
               let uu____3248 =
                 let uu____3249 =
                   let uu____3262 =
                     let uu____3263 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3263  in
                   (binders1, uu____3262)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3249  in
               mk1 uu____3248
           | uu____3270 ->
               let uu____3271 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3271 with
                | N hn ->
                    let uu____3273 =
                      let uu____3274 =
                        let uu____3287 =
                          let uu____3288 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3288  in
                        (binders1, uu____3287)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3274  in
                    mk1 uu____3273
                | M a ->
                    let uu____3296 =
                      let uu____3297 =
                        let uu____3310 =
                          let uu____3317 =
                            let uu____3324 =
                              let uu____3329 =
                                let uu____3330 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____3330  in
                              let uu____3331 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____3329, uu____3331)  in
                            [uu____3324]  in
                          FStar_List.append binders1 uu____3317  in
                        let uu____3344 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____3310, uu____3344)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3297  in
                    mk1 uu____3296))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3422 = f x  in
                    FStar_Util.string_builder_append strb uu____3422);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3429 = f x1  in
                         FStar_Util.string_builder_append strb uu____3429))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____3431 =
              let uu____3436 =
                let uu____3437 = FStar_Syntax_Print.term_to_string t2  in
                let uu____3438 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3437 uu____3438
                 in
              (FStar_Errors.Warning_DependencyFound, uu____3436)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3431  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3450 =
              let uu____3451 = FStar_Syntax_Subst.compress ty  in
              uu____3451.FStar_Syntax_Syntax.n  in
            match uu____3450 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3472 =
                  let uu____3473 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____3473  in
                if uu____3472
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3503 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____3503 s  in
                       let uu____3506 =
                         let uu____3507 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____3507  in
                       if uu____3506
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____3510 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____3510 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3532  ->
                                  match uu____3532 with
                                  | (bv,uu____3542) ->
                                      (non_dependent_or_raise s
                                         bv.FStar_Syntax_Syntax.sort;
                                       FStar_Util.set_add bv s))
                             FStar_Syntax_Syntax.no_names binders1
                            in
                         let ct = FStar_Syntax_Util.comp_result c1  in
                         (non_dependent_or_raise s ct;
                          (let k = n1 - (FStar_List.length binders1)  in
                           if k > (Prims.parse_int "0")
                           then is_non_dependent_arrow ct k
                           else true))
                   with | Not_found  -> false)
            | uu____3556 ->
                ((let uu____3558 =
                    let uu____3563 =
                      let uu____3564 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3564
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3563)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3558);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____3571 =
              let uu____3572 = FStar_Syntax_Subst.compress head2  in
              uu____3572.FStar_Syntax_Syntax.n  in
            match uu____3571 with
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
                  (let uu____3577 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____3577)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3579 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____3579 with
                 | ((uu____3588,ty),uu____3590) ->
                     let uu____3595 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____3595
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1
                          in
                       let uu____3603 =
                         let uu____3604 = FStar_Syntax_Subst.compress res  in
                         uu____3604.FStar_Syntax_Syntax.n  in
                       (match uu____3603 with
                        | FStar_Syntax_Syntax.Tm_app uu____3607 -> true
                        | uu____3622 ->
                            ((let uu____3624 =
                                let uu____3629 =
                                  let uu____3630 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3630
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3629)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3624);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3632 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3633 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3635) ->
                is_valid_application t2
            | uu____3640 -> false  in
          let uu____3641 = is_valid_application head1  in
          if uu____3641
          then
            let uu____3642 =
              let uu____3643 =
                let uu____3658 =
                  FStar_List.map
                    (fun uu____3679  ->
                       match uu____3679 with
                       | (t2,qual) ->
                           let uu____3696 = star_type' env t2  in
                           (uu____3696, qual)) args
                   in
                (head1, uu____3658)  in
              FStar_Syntax_Syntax.Tm_app uu____3643  in
            mk1 uu____3642
          else
            (let uu____3706 =
               let uu____3711 =
                 let uu____3712 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3712
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____3711)  in
             FStar_Errors.raise_err uu____3706)
      | FStar_Syntax_Syntax.Tm_bvar uu____3713 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3714 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3715 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3716 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3740 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____3740 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___84_3748 = env  in
                 let uu____3749 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____3749;
                   subst = (uu___84_3748.subst);
                   tc_const = (uu___84_3748.tc_const)
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
               ((let uu___85_3769 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___85_3769.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___85_3769.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3776 =
            let uu____3777 =
              let uu____3784 = star_type' env t2  in (uu____3784, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____3777  in
          mk1 uu____3776
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3832 =
            let uu____3833 =
              let uu____3860 = star_type' env e  in
              let uu____3861 =
                let uu____3876 =
                  let uu____3883 = star_type' env t2  in
                  FStar_Util.Inl uu____3883  in
                (uu____3876, FStar_Pervasives_Native.None)  in
              (uu____3860, uu____3861, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3833  in
          mk1 uu____3832
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3961 =
            let uu____3962 =
              let uu____3989 = star_type' env e  in
              let uu____3990 =
                let uu____4005 =
                  let uu____4012 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____4012  in
                (uu____4005, FStar_Pervasives_Native.None)  in
              (uu____3989, uu____3990, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3962  in
          mk1 uu____3961
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4043,(uu____4044,FStar_Pervasives_Native.Some uu____4045),uu____4046)
          ->
          let uu____4095 =
            let uu____4100 =
              let uu____4101 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4101
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4100)  in
          FStar_Errors.raise_err uu____4095
      | FStar_Syntax_Syntax.Tm_refine uu____4102 ->
          let uu____4109 =
            let uu____4114 =
              let uu____4115 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4115
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4114)  in
          FStar_Errors.raise_err uu____4109
      | FStar_Syntax_Syntax.Tm_uinst uu____4116 ->
          let uu____4123 =
            let uu____4128 =
              let uu____4129 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4129
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4128)  in
          FStar_Errors.raise_err uu____4123
      | FStar_Syntax_Syntax.Tm_quoted uu____4130 ->
          let uu____4137 =
            let uu____4142 =
              let uu____4143 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s"
                uu____4143
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4142)  in
          FStar_Errors.raise_err uu____4137
      | FStar_Syntax_Syntax.Tm_constant uu____4144 ->
          let uu____4145 =
            let uu____4150 =
              let uu____4151 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4151
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4150)  in
          FStar_Errors.raise_err uu____4145
      | FStar_Syntax_Syntax.Tm_match uu____4152 ->
          let uu____4175 =
            let uu____4180 =
              let uu____4181 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4181
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4180)  in
          FStar_Errors.raise_err uu____4175
      | FStar_Syntax_Syntax.Tm_let uu____4182 ->
          let uu____4195 =
            let uu____4200 =
              let uu____4201 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4201
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4200)  in
          FStar_Errors.raise_err uu____4195
      | FStar_Syntax_Syntax.Tm_uvar uu____4202 ->
          let uu____4219 =
            let uu____4224 =
              let uu____4225 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4225
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4224)  in
          FStar_Errors.raise_err uu____4219
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4226 =
            let uu____4231 =
              let uu____4232 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4232
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4231)  in
          FStar_Errors.raise_err uu____4226
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____4234 = FStar_Syntax_Util.unfold_lazy i  in
          star_type' env uu____4234
      | FStar_Syntax_Syntax.Tm_delayed uu____4237 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___69_4268  ->
    match uu___69_4268 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___68_4275  ->
                match uu___68_4275 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4276 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____4282 =
      let uu____4283 = FStar_Syntax_Subst.compress t  in
      uu____4283.FStar_Syntax_Syntax.n  in
    match uu____4282 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4309 =
            let uu____4310 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____4310  in
          is_C uu____4309  in
        if r
        then
          ((let uu____4326 =
              let uu____4327 =
                FStar_List.for_all
                  (fun uu____4335  ->
                     match uu____4335 with | (h,uu____4341) -> is_C h) args
                 in
              Prims.op_Negation uu____4327  in
            if uu____4326 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4345 =
              let uu____4346 =
                FStar_List.for_all
                  (fun uu____4355  ->
                     match uu____4355 with
                     | (h,uu____4361) ->
                         let uu____4362 = is_C h  in
                         Prims.op_Negation uu____4362) args
                 in
              Prims.op_Negation uu____4346  in
            if uu____4345 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4382 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____4382 with
         | M t1 ->
             ((let uu____4385 = is_C t1  in
               if uu____4385 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4389) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4395) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4401,uu____4402) -> is_C t1
    | uu____4443 -> false
  
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
          let uu____4474 =
            let uu____4475 =
              let uu____4490 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____4491 =
                let uu____4498 =
                  let uu____4503 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____4503)  in
                [uu____4498]  in
              (uu____4490, uu____4491)  in
            FStar_Syntax_Syntax.Tm_app uu____4475  in
          mk1 uu____4474  in
        let uu____4518 =
          let uu____4519 = FStar_Syntax_Syntax.mk_binder p  in [uu____4519]
           in
        FStar_Syntax_Util.abs uu____4518 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___70_4524  ->
    match uu___70_4524 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4525 -> false
  
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
        let return_if uu____4758 =
          match uu____4758 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4789 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4791 =
                       let uu____4792 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____4792  in
                     Prims.op_Negation uu____4791)
                   in
                if uu____4789
                then
                  let uu____4793 =
                    let uu____4798 =
                      let uu____4799 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____4800 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____4801 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4799 uu____4800 uu____4801
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4798)  in
                  FStar_Errors.raise_err uu____4793
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4818 = mk_return env t1 s_e  in
                     ((M t1), uu____4818, u_e)))
               | (M t1,N t2) ->
                   let uu____4821 =
                     let uu____4826 =
                       let uu____4827 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____4828 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____4829 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4827 uu____4828 uu____4829
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4826)
                      in
                   FStar_Errors.raise_err uu____4821)
           in
        let ensure_m env1 e2 =
          let strip_m uu___71_4876 =
            match uu___71_4876 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4892 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____4912 =
                let uu____4917 =
                  let uu____4918 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4918
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4917)  in
              FStar_Errors.raise_error uu____4912 e2.FStar_Syntax_Syntax.pos
          | M uu____4925 ->
              let uu____4926 = check env1 e2 context_nm  in
              strip_m uu____4926
           in
        let uu____4933 =
          let uu____4934 = FStar_Syntax_Subst.compress e  in
          uu____4934.FStar_Syntax_Syntax.n  in
        match uu____4933 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4943 ->
            let uu____4944 = infer env e  in return_if uu____4944
        | FStar_Syntax_Syntax.Tm_name uu____4951 ->
            let uu____4952 = infer env e  in return_if uu____4952
        | FStar_Syntax_Syntax.Tm_fvar uu____4959 ->
            let uu____4960 = infer env e  in return_if uu____4960
        | FStar_Syntax_Syntax.Tm_abs uu____4967 ->
            let uu____4984 = infer env e  in return_if uu____4984
        | FStar_Syntax_Syntax.Tm_constant uu____4991 ->
            let uu____4992 = infer env e  in return_if uu____4992
        | FStar_Syntax_Syntax.Tm_quoted uu____4999 ->
            let uu____5006 = infer env e  in return_if uu____5006
        | FStar_Syntax_Syntax.Tm_app uu____5013 ->
            let uu____5028 = infer env e  in return_if uu____5028
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu____5036 = FStar_Syntax_Util.unfold_lazy i  in
            check env uu____5036 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____5098) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____5104) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____5110,uu____5111) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5152 ->
            let uu____5165 =
              let uu____5166 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5166  in
            failwith uu____5165
        | FStar_Syntax_Syntax.Tm_type uu____5173 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5180 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5199 ->
            let uu____5206 =
              let uu____5207 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5207  in
            failwith uu____5206
        | FStar_Syntax_Syntax.Tm_uvar uu____5214 ->
            let uu____5231 =
              let uu____5232 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5232  in
            failwith uu____5231
        | FStar_Syntax_Syntax.Tm_delayed uu____5239 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5270 =
              let uu____5271 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5271  in
            failwith uu____5270

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
      let uu____5299 =
        let uu____5300 = FStar_Syntax_Subst.compress e  in
        uu____5300.FStar_Syntax_Syntax.n  in
      match uu____5299 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____5318 = FStar_Syntax_Util.unfold_lazy i  in
          infer env uu____5318
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5365;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5366;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5372 =
                  let uu___86_5373 = rc  in
                  let uu____5374 =
                    let uu____5379 =
                      let uu____5380 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____5380  in
                    FStar_Pervasives_Native.Some uu____5379  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___86_5373.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5374;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___86_5373.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____5372
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___87_5390 = env  in
            let uu____5391 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____5391;
              subst = (uu___87_5390.subst);
              tc_const = (uu___87_5390.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____5411  ->
                 match uu____5411 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___88_5424 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___88_5424.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___88_5424.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____5425 =
            FStar_List.fold_left
              (fun uu____5454  ->
                 fun uu____5455  ->
                   match (uu____5454, uu____5455) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____5503 = is_C c  in
                       if uu____5503
                       then
                         let xw =
                           let uu____5511 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5511
                            in
                         let x =
                           let uu___89_5513 = bv  in
                           let uu____5514 =
                             let uu____5517 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____5517  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___89_5513.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___89_5513.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5514
                           }  in
                         let env3 =
                           let uu___90_5519 = env2  in
                           let uu____5520 =
                             let uu____5523 =
                               let uu____5524 =
                                 let uu____5531 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____5531)  in
                               FStar_Syntax_Syntax.NT uu____5524  in
                             uu____5523 :: (env2.subst)  in
                           {
                             env = (uu___90_5519.env);
                             subst = uu____5520;
                             tc_const = (uu___90_5519.tc_const)
                           }  in
                         let uu____5532 =
                           let uu____5535 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____5536 =
                             let uu____5539 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____5539 :: acc  in
                           uu____5535 :: uu____5536  in
                         (env3, uu____5532)
                       else
                         (let x =
                            let uu___91_5544 = bv  in
                            let uu____5545 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___91_5544.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___91_5544.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5545
                            }  in
                          let uu____5548 =
                            let uu____5551 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____5551 :: acc  in
                          (env2, uu____5548))) (env1, []) binders1
             in
          (match uu____5425 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____5571 =
                 let check_what =
                   let uu____5593 = is_monadic rc_opt1  in
                   if uu____5593 then check_m else check_n  in
                 let uu____5607 = check_what env2 body1  in
                 match uu____5607 with
                 | (t,s_body,u_body) ->
                     let uu____5623 =
                       let uu____5624 =
                         let uu____5625 = is_monadic rc_opt1  in
                         if uu____5625 then M t else N t  in
                       comp_of_nm uu____5624  in
                     (uu____5623, s_body, u_body)
                  in
               (match uu____5571 with
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
                                 let uu____5650 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___72_5654  ->
                                           match uu___72_5654 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5655 -> false))
                                    in
                                 if uu____5650
                                 then
                                   let uu____5656 =
                                     FStar_List.filter
                                       (fun uu___73_5660  ->
                                          match uu___73_5660 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5661 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5656
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5670 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___74_5674  ->
                                         match uu___74_5674 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5675 -> false))
                                  in
                               if uu____5670
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___75_5682  ->
                                        match uu___75_5682 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5683 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____5684 =
                                   let uu____5685 =
                                     let uu____5690 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____5690
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5685 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____5684
                               else
                                 (let uu____5692 =
                                    let uu___92_5693 = rc  in
                                    let uu____5694 =
                                      let uu____5699 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____5699
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___92_5693.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5694;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___92_5693.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____5692))
                       in
                    let uu____5700 =
                      let comp1 =
                        let uu____5710 = is_monadic rc_opt1  in
                        let uu____5711 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5710 uu____5711
                         in
                      let uu____5712 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____5712,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____5700 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____5754 =
                             let uu____5755 =
                               let uu____5772 =
                                 let uu____5775 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____5775 s_rc_opt  in
                               (s_binders1, s_body1, uu____5772)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5755  in
                           mk1 uu____5754  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____5785 =
                             let uu____5786 =
                               let uu____5803 =
                                 let uu____5806 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____5806 u_rc_opt  in
                               (u_binders2, u_body2, uu____5803)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5786  in
                           mk1 uu____5785  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5816;_};
            FStar_Syntax_Syntax.fv_delta = uu____5817;
            FStar_Syntax_Syntax.fv_qual = uu____5818;_}
          ->
          let uu____5821 =
            let uu____5826 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5826  in
          (match uu____5821 with
           | (uu____5857,t) ->
               let uu____5859 =
                 let uu____5860 = normalize1 t  in N uu____5860  in
               (uu____5859, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5861;
             FStar_Syntax_Syntax.vars = uu____5862;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5925 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5925 with
           | (unary_op,uu____5947) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6006;
             FStar_Syntax_Syntax.vars = uu____6007;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____6083 = FStar_Syntax_Util.head_and_args e  in
          (match uu____6083 with
           | (unary_op,uu____6105) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6170;
             FStar_Syntax_Syntax.vars = uu____6171;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____6209 = infer env a  in
          (match uu____6209 with
           | (t,s,u) ->
               let uu____6225 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6225 with
                | (head1,uu____6247) ->
                    let uu____6268 =
                      let uu____6269 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____6269  in
                    let uu____6270 =
                      let uu____6273 =
                        let uu____6274 =
                          let uu____6289 =
                            let uu____6292 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6292]  in
                          (head1, uu____6289)  in
                        FStar_Syntax_Syntax.Tm_app uu____6274  in
                      mk1 uu____6273  in
                    let uu____6297 =
                      let uu____6300 =
                        let uu____6301 =
                          let uu____6316 =
                            let uu____6319 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6319]  in
                          (head1, uu____6316)  in
                        FStar_Syntax_Syntax.Tm_app uu____6301  in
                      mk1 uu____6300  in
                    (uu____6268, uu____6270, uu____6297)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6328;
             FStar_Syntax_Syntax.vars = uu____6329;_},(a1,uu____6331)::a2::[])
          ->
          let uu____6373 = infer env a1  in
          (match uu____6373 with
           | (t,s,u) ->
               let uu____6389 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6389 with
                | (head1,uu____6411) ->
                    let uu____6432 =
                      let uu____6435 =
                        let uu____6436 =
                          let uu____6451 =
                            let uu____6454 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6454; a2]  in
                          (head1, uu____6451)  in
                        FStar_Syntax_Syntax.Tm_app uu____6436  in
                      mk1 uu____6435  in
                    let uu____6471 =
                      let uu____6474 =
                        let uu____6475 =
                          let uu____6490 =
                            let uu____6493 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6493; a2]  in
                          (head1, uu____6490)  in
                        FStar_Syntax_Syntax.Tm_app uu____6475  in
                      mk1 uu____6474  in
                    (t, uu____6432, uu____6471)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6514;
             FStar_Syntax_Syntax.vars = uu____6515;_},uu____6516)
          ->
          let uu____6537 =
            let uu____6542 =
              let uu____6543 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6543
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6542)  in
          FStar_Errors.raise_error uu____6537 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6550;
             FStar_Syntax_Syntax.vars = uu____6551;_},uu____6552)
          ->
          let uu____6573 =
            let uu____6578 =
              let uu____6579 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6579
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6578)  in
          FStar_Errors.raise_error uu____6573 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6608 = check_n env head1  in
          (match uu____6608 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6630 =
                   let uu____6631 = FStar_Syntax_Subst.compress t  in
                   uu____6631.FStar_Syntax_Syntax.n  in
                 match uu____6630 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6634 -> true
                 | uu____6647 -> false  in
               let rec flatten1 t =
                 let uu____6666 =
                   let uu____6667 = FStar_Syntax_Subst.compress t  in
                   uu____6667.FStar_Syntax_Syntax.n  in
                 match uu____6666 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6684);
                                FStar_Syntax_Syntax.pos = uu____6685;
                                FStar_Syntax_Syntax.vars = uu____6686;_})
                     when is_arrow t1 ->
                     let uu____6711 = flatten1 t1  in
                     (match uu____6711 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6793,uu____6794)
                     -> flatten1 e1
                 | uu____6835 ->
                     let uu____6836 =
                       let uu____6841 =
                         let uu____6842 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6842
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6841)  in
                     FStar_Errors.raise_err uu____6836
                  in
               let uu____6855 = flatten1 t_head  in
               (match uu____6855 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6915 =
                          let uu____6920 =
                            let uu____6921 = FStar_Util.string_of_int n1  in
                            let uu____6928 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____6939 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6921 uu____6928 uu____6939
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6920)
                           in
                        FStar_Errors.raise_err uu____6915)
                     else ();
                     (let uu____6947 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____6947 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6994 args1 =
                            match uu____6994 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____7068 =
                                       let uu____7069 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____7069.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____7068
                                 | (binders3,[]) ->
                                     let uu____7099 =
                                       let uu____7100 =
                                         let uu____7103 =
                                           let uu____7104 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____7104
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____7103
                                          in
                                       uu____7100.FStar_Syntax_Syntax.n  in
                                     (match uu____7099 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____7129 =
                                            let uu____7130 =
                                              let uu____7131 =
                                                let uu____7144 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____7144)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____7131
                                               in
                                            mk1 uu____7130  in
                                          N uu____7129
                                      | uu____7151 -> failwith "wat?")
                                 | ([],uu____7152::uu____7153) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____7193)::binders3,(arg,uu____7196)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____7249 = FStar_List.splitAt n' binders1  in
                          (match uu____7249 with
                           | (binders2,uu____7281) ->
                               let uu____7306 =
                                 let uu____7327 =
                                   FStar_List.map2
                                     (fun uu____7381  ->
                                        fun uu____7382  ->
                                          match (uu____7381, uu____7382) with
                                          | ((bv,uu____7420),(arg,q)) ->
                                              let uu____7437 =
                                                let uu____7438 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____7438.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____7437 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7457 ->
                                                   let uu____7458 =
                                                     let uu____7463 =
                                                       star_type' env arg  in
                                                     (uu____7463, q)  in
                                                   (uu____7458, [(arg, q)])
                                               | uu____7490 ->
                                                   let uu____7491 =
                                                     check_n env arg  in
                                                   (match uu____7491 with
                                                    | (uu____7514,s_arg,u_arg)
                                                        ->
                                                        let uu____7517 =
                                                          let uu____7524 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____7524
                                                          then
                                                            let uu____7531 =
                                                              let uu____7536
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____7536, q)
                                                               in
                                                            [uu____7531;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____7517))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____7327  in
                               (match uu____7306 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____7635 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____7644 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____7635, uu____7644)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7712) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7718) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7724,uu____7725) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7767 = let uu____7768 = env.tc_const c  in N uu____7768
             in
          (uu____7767, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm,qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7775 ->
          let uu____7788 =
            let uu____7789 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7789  in
          failwith uu____7788
      | FStar_Syntax_Syntax.Tm_type uu____7796 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7803 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7822 ->
          let uu____7829 =
            let uu____7830 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7830  in
          failwith uu____7829
      | FStar_Syntax_Syntax.Tm_uvar uu____7837 ->
          let uu____7854 =
            let uu____7855 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7855  in
          failwith uu____7854
      | FStar_Syntax_Syntax.Tm_delayed uu____7862 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7893 =
            let uu____7894 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7894  in
          failwith uu____7893

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
          let uu____7941 = check_n env e0  in
          match uu____7941 with
          | (uu____7954,s_e0,u_e0) ->
              let uu____7957 =
                let uu____7986 =
                  FStar_List.map
                    (fun b  ->
                       let uu____8047 = FStar_Syntax_Subst.open_branch b  in
                       match uu____8047 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___93_8089 = env  in
                             let uu____8090 =
                               let uu____8091 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____8091
                                in
                             {
                               env = uu____8090;
                               subst = (uu___93_8089.subst);
                               tc_const = (uu___93_8089.tc_const)
                             }  in
                           let uu____8094 = f env1 body  in
                           (match uu____8094 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8166 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____7986  in
              (match uu____7957 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____8268 = FStar_List.hd nms  in
                     match uu____8268 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___76_8274  ->
                          match uu___76_8274 with
                          | M uu____8275 -> true
                          | uu____8276 -> false) nms
                      in
                   let uu____8277 =
                     let uu____8314 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8404  ->
                              match uu____8404 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8581 =
                                         check env original_body (M t2)  in
                                       (match uu____8581 with
                                        | (uu____8618,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8657,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____8314  in
                   (match uu____8277 with
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
                              (fun uu____8841  ->
                                 match uu____8841 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8892 =
                                         let uu____8893 =
                                           let uu____8908 =
                                             let uu____8915 =
                                               let uu____8920 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____8921 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____8920, uu____8921)  in
                                             [uu____8915]  in
                                           (s_body, uu____8908)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8893
                                          in
                                       mk1 uu____8892  in
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
                            let uu____8953 =
                              let uu____8954 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____8954]  in
                            let uu____8955 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____8953 uu____8955
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____8961 =
                              let uu____8968 =
                                let uu____8969 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8969
                                 in
                              [uu____8968]  in
                            let uu____8970 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____8961 uu____8970  in
                          let uu____8973 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____9012 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____8973, uu____9012)
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
                           let uu____9029 =
                             let uu____9032 =
                               let uu____9033 =
                                 let uu____9060 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____9060,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____9033  in
                             mk1 uu____9032  in
                           let uu____9097 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____9029, uu____9097))))

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
              let uu____9146 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____9146]  in
            let uu____9147 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____9147 with
            | (x_binders1,e21) ->
                let uu____9160 = infer env e1  in
                (match uu____9160 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____9177 = is_C t1  in
                       if uu____9177
                       then
                         let uu___94_9178 = binding  in
                         let uu____9179 =
                           let uu____9182 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____9182  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___94_9178.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___94_9178.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9179;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___94_9178.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___94_9178.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___94_9178.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___94_9178.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding  in
                     let env1 =
                       let uu___95_9185 = env  in
                       let uu____9186 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___96_9188 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___96_9188.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___96_9188.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9186;
                         subst = (uu___95_9185.subst);
                         tc_const = (uu___95_9185.tc_const)
                       }  in
                     let uu____9189 = proceed env1 e21  in
                     (match uu____9189 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___97_9206 = binding  in
                            let uu____9207 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___97_9206.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___97_9206.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9207;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___97_9206.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___97_9206.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___97_9206.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___97_9206.FStar_Syntax_Syntax.lbpos)
                            }  in
                          let uu____9210 =
                            let uu____9213 =
                              let uu____9214 =
                                let uu____9227 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___98_9237 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___98_9237.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___98_9237.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___98_9237.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___98_9237.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___98_9237.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___98_9237.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9227)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9214  in
                            mk1 uu____9213  in
                          let uu____9238 =
                            let uu____9241 =
                              let uu____9242 =
                                let uu____9255 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___99_9265 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___99_9265.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___99_9265.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___99_9265.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___99_9265.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___99_9265.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___99_9265.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9255)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9242  in
                            mk1 uu____9241  in
                          (nm_rec, uu____9210, uu____9238))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___100_9274 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___100_9274.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___100_9274.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___100_9274.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___100_9274.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___100_9274.FStar_Syntax_Syntax.lbpos)
                       }  in
                     let env1 =
                       let uu___101_9276 = env  in
                       let uu____9277 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___102_9279 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___102_9279.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___102_9279.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9277;
                         subst = (uu___101_9276.subst);
                         tc_const = (uu___101_9276.tc_const)
                       }  in
                     let uu____9280 = ensure_m env1 e21  in
                     (match uu____9280 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____9303 =
                              let uu____9304 =
                                let uu____9319 =
                                  let uu____9326 =
                                    let uu____9331 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____9332 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9331, uu____9332)  in
                                  [uu____9326]  in
                                (s_e2, uu____9319)  in
                              FStar_Syntax_Syntax.Tm_app uu____9304  in
                            mk1 uu____9303  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____9351 =
                              let uu____9352 =
                                let uu____9367 =
                                  let uu____9374 =
                                    let uu____9379 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____9379)  in
                                  [uu____9374]  in
                                (s_e1, uu____9367)  in
                              FStar_Syntax_Syntax.Tm_app uu____9352  in
                            mk1 uu____9351  in
                          let uu____9394 =
                            let uu____9395 =
                              let uu____9396 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____9396]  in
                            FStar_Syntax_Util.abs uu____9395 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____9397 =
                            let uu____9400 =
                              let uu____9401 =
                                let uu____9414 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___103_9424 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___103_9424.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___103_9424.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___103_9424.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___103_9424.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___103_9424.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___103_9424.FStar_Syntax_Syntax.lbpos)
                                     })]), uu____9414)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9401  in
                            mk1 uu____9400  in
                          ((M t2), uu____9394, uu____9397)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9436 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____9436  in
      let uu____9437 = check env e mn  in
      match uu____9437 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9453 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9475 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____9475  in
      let uu____9476 = check env e mn  in
      match uu____9476 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9492 -> failwith "[check_m]: impossible"

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
        (let uu____9522 =
           let uu____9523 = is_C c  in Prims.op_Negation uu____9523  in
         if uu____9522 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____9533 =
           let uu____9534 = FStar_Syntax_Subst.compress c  in
           uu____9534.FStar_Syntax_Syntax.n  in
         match uu____9533 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9559 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____9559 with
              | (wp_head,wp_args) ->
                  ((let uu____9597 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9611 =
                           let uu____9612 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9612
                            in
                         Prims.op_Negation uu____9611)
                       in
                    if uu____9597 then failwith "mismatch" else ());
                   (let uu____9620 =
                      let uu____9621 =
                        let uu____9636 =
                          FStar_List.map2
                            (fun uu____9664  ->
                               fun uu____9665  ->
                                 match (uu____9664, uu____9665) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9704 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____9704
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____9707 =
                                           let uu____9712 =
                                             let uu____9713 =
                                               print_implicit q  in
                                             let uu____9714 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %b %b\n"
                                               uu____9713 uu____9714
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____9712)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____9707)
                                      else ();
                                      (let uu____9716 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____9716, q)))) args wp_args
                           in
                        (head1, uu____9636)  in
                      FStar_Syntax_Syntax.Tm_app uu____9621  in
                    mk1 uu____9620)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____9750 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____9750 with
              | (binders_orig,comp1) ->
                  let uu____9757 =
                    let uu____9772 =
                      FStar_List.map
                        (fun uu____9806  ->
                           match uu____9806 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____9826 = is_C h  in
                               if uu____9826
                               then
                                 let w' =
                                   let uu____9838 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9838
                                    in
                                 let uu____9839 =
                                   let uu____9846 =
                                     let uu____9853 =
                                       let uu____9858 =
                                         let uu____9859 =
                                           let uu____9860 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____9860  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9859
                                          in
                                       (uu____9858, q)  in
                                     [uu____9853]  in
                                   (w', q) :: uu____9846  in
                                 (w', uu____9839)
                               else
                                 (let x =
                                    let uu____9881 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9881
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____9772  in
                  (match uu____9757 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____9936 =
                           let uu____9939 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9939
                            in
                         FStar_Syntax_Subst.subst_comp uu____9936 comp1  in
                       let app =
                         let uu____9943 =
                           let uu____9944 =
                             let uu____9959 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9974 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____9975 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9974, uu____9975)) bvs
                                in
                             (wp, uu____9959)  in
                           FStar_Syntax_Syntax.Tm_app uu____9944  in
                         mk1 uu____9943  in
                       let comp3 =
                         let uu____9983 = type_of_comp comp2  in
                         let uu____9984 = is_monadic_comp comp2  in
                         trans_G env uu____9983 uu____9984 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9986,uu____9987) ->
             trans_F_ env e wp
         | uu____10028 -> failwith "impossible trans_F_")

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
            let uu____10033 =
              let uu____10034 = star_type' env h  in
              let uu____10037 =
                let uu____10046 =
                  let uu____10051 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____10051)  in
                [uu____10046]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____10034;
                FStar_Syntax_Syntax.effect_args = uu____10037;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____10033
          else
            (let uu____10061 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____10061)

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
    fun t  -> let uu____10080 = n env.env t  in star_type' env uu____10080
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____10099 = n env.env t  in check_n env uu____10099
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____10115 = n env.env c  in
        let uu____10116 = n env.env wp  in
        trans_F_ env uu____10115 uu____10116
  