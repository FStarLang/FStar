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
              let uu___74_93 = a  in
              let uu____94 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___74_93.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___74_93.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____94
              }  in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s  in
            (let uu____102 =
               FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
             if uu____102
             then
               (d "Elaborating extra WP combinators";
                (let uu____104 = FStar_Syntax_Print.term_to_string wp_a1  in
                 FStar_Util.print1 "wp_a is: %s\n" uu____104))
             else ());
            (let rec collect_binders t =
               let uu____116 =
                 let uu____117 =
                   let uu____120 = FStar_Syntax_Subst.compress t  in
                   FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____120
                    in
                 uu____117.FStar_Syntax_Syntax.n  in
               match uu____116 with
               | FStar_Syntax_Syntax.Tm_arrow (bs,comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t1,uu____151) -> t1
                     | uu____160 -> failwith "wp_a contains non-Tot arrow"
                      in
                   let uu____163 = collect_binders rest  in
                   FStar_List.append bs uu____163
               | FStar_Syntax_Syntax.Tm_type uu____174 -> []
               | uu____179 -> failwith "wp_a doesn't end in Type0"  in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name  in
             let gamma =
               let uu____197 = collect_binders wp_a1  in
               FStar_All.pipe_right uu____197 FStar_Syntax_Util.name_binders
                in
             (let uu____217 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")
                 in
              if uu____217
              then
                let uu____218 =
                  let uu____219 =
                    FStar_Syntax_Print.binders_to_string ", " gamma  in
                  FStar_Util.format1 "Gamma is %s\n" uu____219  in
                d uu____218
              else ());
             (let unknown = FStar_Syntax_Syntax.tun  in
              let mk1 x =
                FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
                  FStar_Range.dummyRange
                 in
              let sigelts = FStar_Util.mk_ref []  in
              let register env1 lident def =
                let uu____245 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env1 lident
                    def
                   in
                match uu____245 with
                | (sigelt,fv) ->
                    ((let uu____253 =
                        let uu____256 = FStar_ST.op_Bang sigelts  in sigelt
                          :: uu____256
                         in
                      FStar_ST.op_Colon_Equals sigelts uu____253);
                     fv)
                 in
              let binders_of_list1 =
                FStar_List.map
                  (fun uu____480  ->
                     match uu____480 with
                     | (t,b) ->
                         let uu____491 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____491))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____522 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____522))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____545 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____545)
                 in
              let uu____546 =
                let uu____561 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____583 = f (FStar_Syntax_Syntax.bv_to_name t)
                         in
                      FStar_Syntax_Util.arrow gamma uu____583  in
                    let uu____586 =
                      let uu____587 =
                        let uu____594 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____595 =
                          let uu____598 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____598]  in
                        uu____594 :: uu____595  in
                      FStar_List.append binders uu____587  in
                    FStar_Syntax_Util.abs uu____586 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____603 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____604 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____603, uu____604)  in
                match uu____561 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____638 =
                        let uu____639 =
                          let uu____654 =
                            let uu____661 =
                              FStar_List.map
                                (fun uu____681  ->
                                   match uu____681 with
                                   | (bv,uu____691) ->
                                       let uu____692 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____693 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____692, uu____693)) binders
                               in
                            let uu____694 =
                              let uu____701 =
                                let uu____706 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____707 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____706, uu____707)  in
                              let uu____708 =
                                let uu____715 =
                                  let uu____720 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____720)  in
                                [uu____715]  in
                              uu____701 :: uu____708  in
                            FStar_List.append uu____661 uu____694  in
                          (fv, uu____654)  in
                        FStar_Syntax_Syntax.Tm_app uu____639  in
                      mk1 uu____638  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____546 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____779 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____779
                       in
                    let ret1 =
                      let uu____783 =
                        let uu____784 =
                          let uu____787 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____787  in
                        FStar_Syntax_Util.residual_tot uu____784  in
                      FStar_Pervasives_Native.Some uu____783  in
                    let body =
                      let uu____789 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____789 ret1  in
                    let uu____790 =
                      let uu____791 = mk_all_implicit binders  in
                      let uu____798 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____791 uu____798  in
                    FStar_Syntax_Util.abs uu____790 body ret1  in
                  let c_pure1 =
                    let uu____826 = mk_lid "pure"  in
                    register env1 uu____826 c_pure  in
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
                      let uu____831 =
                        let uu____832 =
                          let uu____833 =
                            let uu____840 =
                              let uu____841 =
                                let uu____842 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____842
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____841  in
                            [uu____840]  in
                          let uu____843 =
                            let uu____846 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____846  in
                          FStar_Syntax_Util.arrow uu____833 uu____843  in
                        mk_gctx uu____832  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____831
                       in
                    let r =
                      let uu____848 =
                        let uu____849 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____849  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____848
                       in
                    let ret1 =
                      let uu____853 =
                        let uu____854 =
                          let uu____857 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____857  in
                        FStar_Syntax_Util.residual_tot uu____854  in
                      FStar_Pervasives_Native.Some uu____853  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____865 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____868 =
                          let uu____877 =
                            let uu____880 =
                              let uu____881 =
                                let uu____882 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____882
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____881  in
                            [uu____880]  in
                          FStar_List.append gamma_as_args uu____877  in
                        FStar_Syntax_Util.mk_app uu____865 uu____868  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____885 =
                      let uu____886 = mk_all_implicit binders  in
                      let uu____893 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____886 uu____893  in
                    FStar_Syntax_Util.abs uu____885 outer_body ret1  in
                  let c_app1 =
                    let uu____929 = mk_lid "app"  in
                    register env1 uu____929 c_app  in
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
                      let uu____936 =
                        let uu____943 =
                          let uu____944 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____944  in
                        [uu____943]  in
                      let uu____945 =
                        let uu____948 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____948  in
                      FStar_Syntax_Util.arrow uu____936 uu____945  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____951 =
                        let uu____952 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____952  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____951
                       in
                    let ret1 =
                      let uu____956 =
                        let uu____957 =
                          let uu____960 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____960  in
                        FStar_Syntax_Util.residual_tot uu____957  in
                      FStar_Pervasives_Native.Some uu____956  in
                    let uu____961 =
                      let uu____962 = mk_all_implicit binders  in
                      let uu____969 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____962 uu____969  in
                    let uu____1004 =
                      let uu____1005 =
                        let uu____1014 =
                          let uu____1017 =
                            let uu____1020 =
                              let uu____1029 =
                                let uu____1032 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____1032]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1029
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1020  in
                          let uu____1033 =
                            let uu____1038 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____1038]  in
                          uu____1017 :: uu____1033  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1014
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1005  in
                    FStar_Syntax_Util.abs uu____961 uu____1004 ret1  in
                  let c_lift11 =
                    let uu____1042 = mk_lid "lift1"  in
                    register env1 uu____1042 c_lift1  in
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
                      let uu____1050 =
                        let uu____1057 =
                          let uu____1058 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1058  in
                        let uu____1059 =
                          let uu____1062 =
                            let uu____1063 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1063  in
                          [uu____1062]  in
                        uu____1057 :: uu____1059  in
                      let uu____1064 =
                        let uu____1067 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1067  in
                      FStar_Syntax_Util.arrow uu____1050 uu____1064  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1070 =
                        let uu____1071 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1071  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1070
                       in
                    let a2 =
                      let uu____1073 =
                        let uu____1074 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1074  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1073
                       in
                    let ret1 =
                      let uu____1078 =
                        let uu____1079 =
                          let uu____1082 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1082  in
                        FStar_Syntax_Util.residual_tot uu____1079  in
                      FStar_Pervasives_Native.Some uu____1078  in
                    let uu____1083 =
                      let uu____1084 = mk_all_implicit binders  in
                      let uu____1091 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1084 uu____1091  in
                    let uu____1134 =
                      let uu____1135 =
                        let uu____1144 =
                          let uu____1147 =
                            let uu____1150 =
                              let uu____1159 =
                                let uu____1162 =
                                  let uu____1165 =
                                    let uu____1174 =
                                      let uu____1177 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1177]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1174
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1165
                                   in
                                let uu____1178 =
                                  let uu____1183 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1183]  in
                                uu____1162 :: uu____1178  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1159
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1150  in
                          let uu____1186 =
                            let uu____1191 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1191]  in
                          uu____1147 :: uu____1186  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1144
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1135  in
                    FStar_Syntax_Util.abs uu____1083 uu____1134 ret1  in
                  let c_lift21 =
                    let uu____1195 = mk_lid "lift2"  in
                    register env1 uu____1195 c_lift2  in
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
                      let uu____1202 =
                        let uu____1209 =
                          let uu____1210 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1210  in
                        [uu____1209]  in
                      let uu____1211 =
                        let uu____1214 =
                          let uu____1215 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1215  in
                        FStar_Syntax_Syntax.mk_Total uu____1214  in
                      FStar_Syntax_Util.arrow uu____1202 uu____1211  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1220 =
                        let uu____1221 =
                          let uu____1224 =
                            let uu____1225 =
                              let uu____1232 =
                                let uu____1233 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1233
                                 in
                              [uu____1232]  in
                            let uu____1234 =
                              let uu____1237 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1237  in
                            FStar_Syntax_Util.arrow uu____1225 uu____1234  in
                          mk_ctx uu____1224  in
                        FStar_Syntax_Util.residual_tot uu____1221  in
                      FStar_Pervasives_Native.Some uu____1220  in
                    let e1 =
                      let uu____1239 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1239
                       in
                    let body =
                      let uu____1241 =
                        let uu____1242 =
                          let uu____1249 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1249]  in
                        FStar_List.append gamma uu____1242  in
                      let uu____1254 =
                        let uu____1255 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1258 =
                          let uu____1267 =
                            let uu____1268 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1268  in
                          let uu____1269 = args_of_binders1 gamma  in
                          uu____1267 :: uu____1269  in
                        FStar_Syntax_Util.mk_app uu____1255 uu____1258  in
                      FStar_Syntax_Util.abs uu____1241 uu____1254 ret1  in
                    let uu____1272 =
                      let uu____1273 = mk_all_implicit binders  in
                      let uu____1280 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1273 uu____1280  in
                    FStar_Syntax_Util.abs uu____1272 body ret1  in
                  let c_push1 =
                    let uu____1312 = mk_lid "push"  in
                    register env1 uu____1312 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1332 =
                        let uu____1333 =
                          let uu____1348 = args_of_binders1 binders  in
                          (c, uu____1348)  in
                        FStar_Syntax_Syntax.Tm_app uu____1333  in
                      mk1 uu____1332
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1358 =
                        let uu____1359 =
                          let uu____1366 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1367 =
                            let uu____1370 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1370]  in
                          uu____1366 :: uu____1367  in
                        let uu____1371 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1359 uu____1371  in
                      FStar_Syntax_Syntax.mk_Total uu____1358  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1375 =
                      let uu____1376 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1376  in
                    let uu____1387 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1389 =
                        let uu____1392 =
                          let uu____1401 =
                            let uu____1404 =
                              let uu____1407 =
                                let uu____1416 =
                                  let uu____1417 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1417  in
                                [uu____1416]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1407  in
                            [uu____1404]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1401
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1392  in
                      FStar_Syntax_Util.ascribe uu____1389
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1375 uu____1387
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1437 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1437 wp_if_then_else  in
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
                      let uu____1448 =
                        let uu____1457 =
                          let uu____1460 =
                            let uu____1463 =
                              let uu____1472 =
                                let uu____1475 =
                                  let uu____1478 =
                                    let uu____1487 =
                                      let uu____1488 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1488
                                       in
                                    [uu____1487]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1478
                                   in
                                [uu____1475]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1472
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1463  in
                          let uu____1493 =
                            let uu____1498 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1498]  in
                          uu____1460 :: uu____1493  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1457
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1448  in
                    let uu____1501 =
                      let uu____1502 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1502  in
                    FStar_Syntax_Util.abs uu____1501 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1514 = mk_lid "wp_assert"  in
                    register env1 uu____1514 wp_assert  in
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
                      let uu____1525 =
                        let uu____1534 =
                          let uu____1537 =
                            let uu____1540 =
                              let uu____1549 =
                                let uu____1552 =
                                  let uu____1555 =
                                    let uu____1564 =
                                      let uu____1565 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1565
                                       in
                                    [uu____1564]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1555
                                   in
                                [uu____1552]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1549
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1540  in
                          let uu____1570 =
                            let uu____1575 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1575]  in
                          uu____1537 :: uu____1570  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1534
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1525  in
                    let uu____1578 =
                      let uu____1579 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1579  in
                    FStar_Syntax_Util.abs uu____1578 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1591 = mk_lid "wp_assume"  in
                    register env1 uu____1591 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1600 =
                        let uu____1607 =
                          let uu____1608 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1608  in
                        [uu____1607]  in
                      let uu____1609 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1600 uu____1609  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1616 =
                        let uu____1625 =
                          let uu____1628 =
                            let uu____1631 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1631  in
                          let uu____1640 =
                            let uu____1645 =
                              let uu____1648 =
                                let uu____1657 =
                                  let uu____1660 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1660]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1657
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1648  in
                            [uu____1645]  in
                          uu____1628 :: uu____1640  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1625
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1616  in
                    let uu____1667 =
                      let uu____1668 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1668  in
                    FStar_Syntax_Util.abs uu____1667 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1680 = mk_lid "wp_close"  in
                    register env1 uu____1680 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____1690 =
                      let uu____1691 =
                        let uu____1692 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1692
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1691  in
                    FStar_Pervasives_Native.Some uu____1690  in
                  let mk_forall1 x body =
                    let uu____1704 =
                      let uu____1707 =
                        let uu____1708 =
                          let uu____1723 =
                            let uu____1726 =
                              let uu____1727 =
                                let uu____1728 =
                                  let uu____1729 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1729]  in
                                FStar_Syntax_Util.abs uu____1728 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1727  in
                            [uu____1726]  in
                          (FStar_Syntax_Util.tforall, uu____1723)  in
                        FStar_Syntax_Syntax.Tm_app uu____1708  in
                      FStar_Syntax_Syntax.mk uu____1707  in
                    uu____1704 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____1739 =
                      let uu____1740 = FStar_Syntax_Subst.compress t  in
                      uu____1740.FStar_Syntax_Syntax.n  in
                    match uu____1739 with
                    | FStar_Syntax_Syntax.Tm_type uu____1743 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1769  ->
                              match uu____1769 with
                              | (b,uu____1775) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1776 -> true  in
                  let rec is_monotonic t =
                    let uu____1781 =
                      let uu____1782 = FStar_Syntax_Subst.compress t  in
                      uu____1782.FStar_Syntax_Syntax.n  in
                    match uu____1781 with
                    | FStar_Syntax_Syntax.Tm_type uu____1785 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1811  ->
                              match uu____1811 with
                              | (b,uu____1817) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1818 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____1870 =
                      let uu____1871 = FStar_Syntax_Subst.compress t1  in
                      uu____1871.FStar_Syntax_Syntax.n  in
                    match uu____1870 with
                    | FStar_Syntax_Syntax.Tm_type uu____1874 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1877);
                                      FStar_Syntax_Syntax.pos = uu____1878;
                                      FStar_Syntax_Syntax.vars = uu____1879;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1913 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1913
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____1916 =
                              let uu____1919 =
                                let uu____1928 =
                                  let uu____1929 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1929  in
                                [uu____1928]  in
                              FStar_Syntax_Util.mk_app x uu____1919  in
                            let uu____1930 =
                              let uu____1933 =
                                let uu____1942 =
                                  let uu____1943 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1943  in
                                [uu____1942]  in
                              FStar_Syntax_Util.mk_app y uu____1933  in
                            mk_rel1 b uu____1916 uu____1930  in
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
                             let uu____1948 =
                               let uu____1949 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1952 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1949 uu____1952  in
                             let uu____1955 =
                               let uu____1956 =
                                 let uu____1959 =
                                   let uu____1968 =
                                     let uu____1969 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1969
                                      in
                                   [uu____1968]  in
                                 FStar_Syntax_Util.mk_app x uu____1959  in
                               let uu____1970 =
                                 let uu____1973 =
                                   let uu____1982 =
                                     let uu____1983 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1983
                                      in
                                   [uu____1982]  in
                                 FStar_Syntax_Util.mk_app y uu____1973  in
                               mk_rel1 b uu____1956 uu____1970  in
                             FStar_Syntax_Util.mk_imp uu____1948 uu____1955
                              in
                           let uu____1984 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1984)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1987);
                                      FStar_Syntax_Syntax.pos = uu____1988;
                                      FStar_Syntax_Syntax.vars = uu____1989;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____2023 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____2023
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____2026 =
                              let uu____2029 =
                                let uu____2038 =
                                  let uu____2039 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2039  in
                                [uu____2038]  in
                              FStar_Syntax_Util.mk_app x uu____2029  in
                            let uu____2040 =
                              let uu____2043 =
                                let uu____2052 =
                                  let uu____2053 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____2053  in
                                [uu____2052]  in
                              FStar_Syntax_Util.mk_app y uu____2043  in
                            mk_rel1 b uu____2026 uu____2040  in
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
                             let uu____2058 =
                               let uu____2059 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2062 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____2059 uu____2062  in
                             let uu____2065 =
                               let uu____2066 =
                                 let uu____2069 =
                                   let uu____2078 =
                                     let uu____2079 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2079
                                      in
                                   [uu____2078]  in
                                 FStar_Syntax_Util.mk_app x uu____2069  in
                               let uu____2080 =
                                 let uu____2083 =
                                   let uu____2092 =
                                     let uu____2093 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2093
                                      in
                                   [uu____2092]  in
                                 FStar_Syntax_Util.mk_app y uu____2083  in
                               mk_rel1 b uu____2066 uu____2080  in
                             FStar_Syntax_Util.mk_imp uu____2058 uu____2065
                              in
                           let uu____2094 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2094)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___75_2125 = t1  in
                          let uu____2126 =
                            let uu____2127 =
                              let uu____2140 =
                                let uu____2141 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2141  in
                              ([binder], uu____2140)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2127  in
                          {
                            FStar_Syntax_Syntax.n = uu____2126;
                            FStar_Syntax_Syntax.pos =
                              (uu___75_2125.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___75_2125.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2156 ->
                        failwith "unhandled arrow"
                    | uu____2169 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                          FStar_Syntax_Util.is_tuple_constructor uu____2211
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2226 =
                                let uu____2227 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2227 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2226
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2254 =
                            let uu____2261 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2275  ->
                                     match uu____2275 with
                                     | (t2,q) ->
                                         let uu____2282 = project i x  in
                                         let uu____2283 = project i y  in
                                         mk_stronger t2 uu____2282 uu____2283)
                                args
                               in
                            match uu____2261 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2254 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2310);
                                      FStar_Syntax_Syntax.pos = uu____2311;
                                      FStar_Syntax_Syntax.vars = uu____2312;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2350  ->
                                   match uu____2350 with
                                   | (bv,q) ->
                                       let uu____2357 =
                                         let uu____2358 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2358  in
                                       FStar_Syntax_Syntax.gen_bv uu____2357
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2365 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2365) bvs
                             in
                          let body =
                            let uu____2367 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2368 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2367 uu____2368  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2375);
                                      FStar_Syntax_Syntax.pos = uu____2376;
                                      FStar_Syntax_Syntax.vars = uu____2377;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2415  ->
                                   match uu____2415 with
                                   | (bv,q) ->
                                       let uu____2422 =
                                         let uu____2423 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2423  in
                                       FStar_Syntax_Syntax.gen_bv uu____2422
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2430 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2430) bvs
                             in
                          let body =
                            let uu____2432 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2433 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2432 uu____2433  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2438 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____2440 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____2441 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____2442 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____2440 uu____2441 uu____2442  in
                    let uu____2443 =
                      let uu____2444 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____2444  in
                    FStar_Syntax_Util.abs uu____2443 body ret_tot_type  in
                  let stronger1 =
                    let uu____2472 = mk_lid "stronger"  in
                    register env1 uu____2472 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2478 = FStar_Util.prefix gamma  in
                    match uu____2478 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____2523 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2523
                             in
                          let uu____2526 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____2526 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2536 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____2536  in
                              let guard_free1 =
                                let uu____2546 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____2546  in
                              let pat =
                                let uu____2550 =
                                  let uu____2559 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____2559]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2550
                                 in
                              let pattern_guarded_body =
                                let uu____2563 =
                                  let uu____2564 =
                                    let uu____2571 =
                                      let uu____2572 =
                                        let uu____2583 =
                                          let uu____2586 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____2586]  in
                                        [uu____2583]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2572
                                       in
                                    (body, uu____2571)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____2564  in
                                mk1 uu____2563  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2591 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____2595 =
                            let uu____2596 =
                              let uu____2597 =
                                let uu____2598 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____2601 =
                                  let uu____2610 = args_of_binders1 wp_args
                                     in
                                  let uu____2613 =
                                    let uu____2616 =
                                      let uu____2617 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____2617
                                       in
                                    [uu____2616]  in
                                  FStar_List.append uu____2610 uu____2613  in
                                FStar_Syntax_Util.mk_app uu____2598
                                  uu____2601
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2597  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2596
                             in
                          FStar_Syntax_Util.abs gamma uu____2595
                            ret_gtot_type
                           in
                        let uu____2618 =
                          let uu____2619 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____2619  in
                        FStar_Syntax_Util.abs uu____2618 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____2631 = mk_lid "wp_ite"  in
                    register env1 uu____2631 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2637 = FStar_Util.prefix gamma  in
                    match uu____2637 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____2680 =
                            let uu____2681 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____2684 =
                              let uu____2693 =
                                let uu____2694 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____2694  in
                              [uu____2693]  in
                            FStar_Syntax_Util.mk_app uu____2681 uu____2684
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2680
                           in
                        let uu____2695 =
                          let uu____2696 =
                            let uu____2703 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____2703 gamma  in
                          FStar_List.append binders uu____2696  in
                        FStar_Syntax_Util.abs uu____2695 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____2719 = mk_lid "null_wp"  in
                    register env1 uu____2719 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____2728 =
                        let uu____2737 =
                          let uu____2740 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____2741 =
                            let uu____2744 =
                              let uu____2747 =
                                let uu____2756 =
                                  let uu____2757 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____2757  in
                                [uu____2756]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2747
                               in
                            let uu____2758 =
                              let uu____2763 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____2763]  in
                            uu____2744 :: uu____2758  in
                          uu____2740 :: uu____2741  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2737
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____2728  in
                    let uu____2766 =
                      let uu____2767 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____2767  in
                    FStar_Syntax_Util.abs uu____2766 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____2779 = mk_lid "wp_trivial"  in
                    register env1 uu____2779 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____2784 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____2784
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____2789 =
                      let uu____2792 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____2792  in
                    let uu____2892 =
                      let uu___76_2893 = ed  in
                      let uu____2894 =
                        let uu____2895 = c wp_if_then_else2  in
                        ([], uu____2895)  in
                      let uu____2898 =
                        let uu____2899 = c wp_ite2  in ([], uu____2899)  in
                      let uu____2902 =
                        let uu____2903 = c stronger2  in ([], uu____2903)  in
                      let uu____2906 =
                        let uu____2907 = c wp_close2  in ([], uu____2907)  in
                      let uu____2910 =
                        let uu____2911 = c wp_assert2  in ([], uu____2911)
                         in
                      let uu____2914 =
                        let uu____2915 = c wp_assume2  in ([], uu____2915)
                         in
                      let uu____2918 =
                        let uu____2919 = c null_wp2  in ([], uu____2919)  in
                      let uu____2922 =
                        let uu____2923 = c wp_trivial2  in ([], uu____2923)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___76_2893.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___76_2893.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___76_2893.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___76_2893.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___76_2893.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___76_2893.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___76_2893.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2894;
                        FStar_Syntax_Syntax.ite_wp = uu____2898;
                        FStar_Syntax_Syntax.stronger = uu____2902;
                        FStar_Syntax_Syntax.close_wp = uu____2906;
                        FStar_Syntax_Syntax.assert_p = uu____2910;
                        FStar_Syntax_Syntax.assume_p = uu____2914;
                        FStar_Syntax_Syntax.null_wp = uu____2918;
                        FStar_Syntax_Syntax.trivial = uu____2922;
                        FStar_Syntax_Syntax.repr =
                          (uu___76_2893.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___76_2893.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___76_2893.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___76_2893.FStar_Syntax_Syntax.actions)
                      }  in
                    (uu____2789, uu____2892)))))
  
type env_ = env[@@deriving show]
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env  -> env.env 
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env  ->
    fun env'  ->
      let uu___77_2937 = dmff_env  in
      {
        env = env';
        subst = (uu___77_2937.subst);
        tc_const = (uu___77_2937.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let (uu___is_N : nm -> Prims.bool) =
  fun projectee  -> match projectee with | N _0 -> true | uu____2950 -> false 
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | N _0 -> _0 
let (uu___is_M : nm -> Prims.bool) =
  fun projectee  -> match projectee with | M _0 -> true | uu____2962 -> false 
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let (nm_of_comp : FStar_Syntax_Syntax.comp' -> nm) =
  fun uu___63_2972  ->
    match uu___63_2972 with
    | FStar_Syntax_Syntax.Total (t,uu____2974) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___62_2987  ->
                match uu___62_2987 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2988 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2990 =
          let uu____2991 =
            let uu____2992 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2992
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2991  in
        failwith uu____2990
    | FStar_Syntax_Syntax.GTotal uu____2993 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let (string_of_nm : nm -> Prims.string) =
  fun uu___64_3004  ->
    match uu___64_3004 with
    | N t ->
        let uu____3006 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____3006
    | M t ->
        let uu____3008 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____3008
  
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____3012,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____3014;
                      FStar_Syntax_Syntax.vars = uu____3015;_})
        -> nm_of_comp n2
    | uu____3032 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    let uu____3040 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____3040 with | M uu____3041 -> true | N uu____3042 -> false
  
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____3046 -> false
  
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ  ->
    let star_once typ1 =
      let uu____3056 =
        let uu____3063 =
          let uu____3064 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____3064  in
        [uu____3063]  in
      let uu____3065 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____3056 uu____3065  in
    let uu____3068 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____3068
  
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
          (let uu____3105 =
             let uu____3118 =
               let uu____3125 =
                 let uu____3130 =
                   let uu____3131 = star_type' env a  in
                   FStar_Syntax_Syntax.null_bv uu____3131  in
                 let uu____3132 = FStar_Syntax_Syntax.as_implicit false  in
                 (uu____3130, uu____3132)  in
               [uu____3125]  in
             let uu____3141 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
             (uu____3118, uu____3141)  in
           FStar_Syntax_Syntax.Tm_arrow uu____3105)

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3169) ->
          let binders1 =
            FStar_List.map
              (fun uu____3205  ->
                 match uu____3205 with
                 | (bv,aqual) ->
                     let uu____3216 =
                       let uu___78_3217 = bv  in
                       let uu____3218 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___78_3217.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___78_3217.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3218
                       }  in
                     (uu____3216, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3221,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3223);
                             FStar_Syntax_Syntax.pos = uu____3224;
                             FStar_Syntax_Syntax.vars = uu____3225;_})
               ->
               let uu____3250 =
                 let uu____3251 =
                   let uu____3264 =
                     let uu____3265 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3265  in
                   (binders1, uu____3264)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3251  in
               mk1 uu____3250
           | uu____3272 ->
               let uu____3273 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3273 with
                | N hn ->
                    let uu____3275 =
                      let uu____3276 =
                        let uu____3289 =
                          let uu____3290 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3290  in
                        (binders1, uu____3289)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3276  in
                    mk1 uu____3275
                | M a ->
                    let uu____3298 =
                      let uu____3299 =
                        let uu____3312 =
                          let uu____3319 =
                            let uu____3326 =
                              let uu____3331 =
                                let uu____3332 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____3332  in
                              let uu____3333 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____3331, uu____3333)  in
                            [uu____3326]  in
                          FStar_List.append binders1 uu____3319  in
                        let uu____3346 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____3312, uu____3346)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3299  in
                    mk1 uu____3298))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3416 = f x  in
                    FStar_Util.string_builder_append strb uu____3416);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3423 = f x1  in
                         FStar_Util.string_builder_append strb uu____3423))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____3425 =
              let uu____3430 =
                let uu____3431 = FStar_Syntax_Print.term_to_string t2  in
                let uu____3432 =
                  string_of_set FStar_Syntax_Print.bv_to_string s  in
                FStar_Util.format2 "Dependency found in term %s : %s"
                  uu____3431 uu____3432
                 in
              (FStar_Errors.Warning_DependencyFound, uu____3430)  in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____3425  in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3440 =
              let uu____3441 = FStar_Syntax_Subst.compress ty  in
              uu____3441.FStar_Syntax_Syntax.n  in
            match uu____3440 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3462 =
                  let uu____3463 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____3463  in
                if uu____3462
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3489 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____3489 s  in
                       let uu____3492 =
                         let uu____3493 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____3493  in
                       if uu____3492
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____3496 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____3496 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3518  ->
                                  match uu____3518 with
                                  | (bv,uu____3528) ->
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
            | uu____3542 ->
                ((let uu____3544 =
                    let uu____3549 =
                      let uu____3550 = FStar_Syntax_Print.term_to_string ty
                         in
                      FStar_Util.format1 "Not a dependent arrow : %s"
                        uu____3550
                       in
                    (FStar_Errors.Warning_NotDependentArrow, uu____3549)  in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos
                    uu____3544);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____3555 =
              let uu____3556 = FStar_Syntax_Subst.compress head2  in
              uu____3556.FStar_Syntax_Syntax.n  in
            match uu____3555 with
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
                  (let uu____3561 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____3561)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3563 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____3563 with
                 | ((uu____3572,ty),uu____3574) ->
                     let uu____3579 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____3579
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1
                          in
                       let uu____3587 =
                         let uu____3588 = FStar_Syntax_Subst.compress res  in
                         uu____3588.FStar_Syntax_Syntax.n  in
                       (match uu____3587 with
                        | FStar_Syntax_Syntax.Tm_app uu____3591 -> true
                        | uu____3606 ->
                            ((let uu____3608 =
                                let uu____3613 =
                                  let uu____3614 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu____3614
                                   in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu____3613)
                                 in
                              FStar_Errors.log_issue
                                head2.FStar_Syntax_Syntax.pos uu____3608);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3616 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3617 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3619) ->
                is_valid_application t2
            | uu____3624 -> false  in
          let uu____3625 = is_valid_application head1  in
          if uu____3625
          then
            let uu____3626 =
              let uu____3627 =
                let uu____3642 =
                  FStar_List.map
                    (fun uu____3663  ->
                       match uu____3663 with
                       | (t2,qual) ->
                           let uu____3680 = star_type' env t2  in
                           (uu____3680, qual)) args
                   in
                (head1, uu____3642)  in
              FStar_Syntax_Syntax.Tm_app uu____3627  in
            mk1 uu____3626
          else
            (let uu____3690 =
               let uu____3695 =
                 let uu____3696 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3696
                  in
               (FStar_Errors.Fatal_WrongTerm, uu____3695)  in
             FStar_Errors.raise_err uu____3690)
      | FStar_Syntax_Syntax.Tm_bvar uu____3697 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3698 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3699 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3700 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3724 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____3724 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___81_3732 = env  in
                 let uu____3733 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____3733;
                   subst = (uu___81_3732.subst);
                   tc_const = (uu___81_3732.tc_const)
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
               ((let uu___82_3753 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___82_3753.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___82_3753.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3760 =
            let uu____3761 =
              let uu____3768 = star_type' env t2  in (uu____3768, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____3761  in
          mk1 uu____3760
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3816 =
            let uu____3817 =
              let uu____3844 = star_type' env e  in
              let uu____3845 =
                let uu____3860 =
                  let uu____3867 = star_type' env t2  in
                  FStar_Util.Inl uu____3867  in
                (uu____3860, FStar_Pervasives_Native.None)  in
              (uu____3844, uu____3845, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3817  in
          mk1 uu____3816
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3945 =
            let uu____3946 =
              let uu____3973 = star_type' env e  in
              let uu____3974 =
                let uu____3989 =
                  let uu____3996 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____3996  in
                (uu____3989, FStar_Pervasives_Native.None)  in
              (uu____3973, uu____3974, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3946  in
          mk1 uu____3945
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____4027,(uu____4028,FStar_Pervasives_Native.Some uu____4029),uu____4030)
          ->
          let uu____4079 =
            let uu____4084 =
              let uu____4085 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu____4085
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4084)  in
          FStar_Errors.raise_err uu____4079
      | FStar_Syntax_Syntax.Tm_refine uu____4086 ->
          let uu____4093 =
            let uu____4098 =
              let uu____4099 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____4099
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4098)  in
          FStar_Errors.raise_err uu____4093
      | FStar_Syntax_Syntax.Tm_uinst uu____4100 ->
          let uu____4107 =
            let uu____4112 =
              let uu____4113 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____4113
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4112)  in
          FStar_Errors.raise_err uu____4107
      | FStar_Syntax_Syntax.Tm_constant uu____4114 ->
          let uu____4115 =
            let uu____4120 =
              let uu____4121 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____4121
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4120)  in
          FStar_Errors.raise_err uu____4115
      | FStar_Syntax_Syntax.Tm_match uu____4122 ->
          let uu____4145 =
            let uu____4150 =
              let uu____4151 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____4151
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4150)  in
          FStar_Errors.raise_err uu____4145
      | FStar_Syntax_Syntax.Tm_let uu____4152 ->
          let uu____4165 =
            let uu____4170 =
              let uu____4171 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____4171
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4170)  in
          FStar_Errors.raise_err uu____4165
      | FStar_Syntax_Syntax.Tm_uvar uu____4172 ->
          let uu____4189 =
            let uu____4194 =
              let uu____4195 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____4195
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4194)  in
          FStar_Errors.raise_err uu____4189
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____4196 =
            let uu____4201 =
              let uu____4202 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____4202
               in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu____4201)  in
          FStar_Errors.raise_err uu____4196
      | FStar_Syntax_Syntax.Tm_delayed uu____4203 -> failwith "impossible"

let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___66_4232  ->
    match uu___66_4232 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___65_4239  ->
                match uu___65_4239 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4240 -> false))
  
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    let uu____4244 =
      let uu____4245 = FStar_Syntax_Subst.compress t  in
      uu____4245.FStar_Syntax_Syntax.n  in
    match uu____4244 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4271 =
            let uu____4272 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____4272  in
          is_C uu____4271  in
        if r
        then
          ((let uu____4288 =
              let uu____4289 =
                FStar_List.for_all
                  (fun uu____4297  ->
                     match uu____4297 with | (h,uu____4303) -> is_C h) args
                 in
              Prims.op_Negation uu____4289  in
            if uu____4288 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4307 =
              let uu____4308 =
                FStar_List.for_all
                  (fun uu____4317  ->
                     match uu____4317 with
                     | (h,uu____4323) ->
                         let uu____4324 = is_C h  in
                         Prims.op_Negation uu____4324) args
                 in
              Prims.op_Negation uu____4308  in
            if uu____4307 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4344 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____4344 with
         | M t1 ->
             ((let uu____4347 = is_C t1  in
               if uu____4347 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4351) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4357) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4363,uu____4364) -> is_C t1
    | uu____4405 -> false
  
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
          let uu____4428 =
            let uu____4429 =
              let uu____4444 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____4445 =
                let uu____4452 =
                  let uu____4457 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____4457)  in
                [uu____4452]  in
              (uu____4444, uu____4445)  in
            FStar_Syntax_Syntax.Tm_app uu____4429  in
          mk1 uu____4428  in
        let uu____4472 =
          let uu____4473 = FStar_Syntax_Syntax.mk_binder p  in [uu____4473]
           in
        FStar_Syntax_Util.abs uu____4472 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___67_4476  ->
    match uu___67_4476 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4477 -> false
  
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
        let return_if uu____4652 =
          match uu____4652 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4679 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4681 =
                       let uu____4682 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____4682  in
                     Prims.op_Negation uu____4681)
                   in
                if uu____4679
                then
                  let uu____4683 =
                    let uu____4688 =
                      let uu____4689 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____4690 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____4691 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4689 uu____4690 uu____4691
                       in
                    (FStar_Errors.Fatal_TypeMismatch, uu____4688)  in
                  FStar_Errors.raise_err uu____4683
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4708 = mk_return env t1 s_e  in
                     ((M t1), uu____4708, u_e)))
               | (M t1,N t2) ->
                   let uu____4711 =
                     let uu____4716 =
                       let uu____4717 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____4718 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____4719 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4717 uu____4718 uu____4719
                        in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu____4716)
                      in
                   FStar_Errors.raise_err uu____4711)
           in
        let ensure_m env1 e2 =
          let strip_m uu___68_4760 =
            match uu___68_4760 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4776 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____4796 =
                let uu____4801 =
                  let uu____4802 = FStar_Syntax_Print.term_to_string t  in
                  Prims.strcat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu____4802
                   in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu____4801)  in
              FStar_Errors.raise_error uu____4796 e2.FStar_Syntax_Syntax.pos
          | M uu____4809 ->
              let uu____4810 = check env1 e2 context_nm  in
              strip_m uu____4810
           in
        let uu____4817 =
          let uu____4818 = FStar_Syntax_Subst.compress e  in
          uu____4818.FStar_Syntax_Syntax.n  in
        match uu____4817 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4827 ->
            let uu____4828 = infer env e  in return_if uu____4828
        | FStar_Syntax_Syntax.Tm_name uu____4835 ->
            let uu____4836 = infer env e  in return_if uu____4836
        | FStar_Syntax_Syntax.Tm_fvar uu____4843 ->
            let uu____4844 = infer env e  in return_if uu____4844
        | FStar_Syntax_Syntax.Tm_abs uu____4851 ->
            let uu____4868 = infer env e  in return_if uu____4868
        | FStar_Syntax_Syntax.Tm_constant uu____4875 ->
            let uu____4876 = infer env e  in return_if uu____4876
        | FStar_Syntax_Syntax.Tm_app uu____4883 ->
            let uu____4898 = infer env e  in return_if uu____4898
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4966) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4972) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4978,uu____4979) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____5020 ->
            let uu____5033 =
              let uu____5034 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____5034  in
            failwith uu____5033
        | FStar_Syntax_Syntax.Tm_type uu____5041 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____5048 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____5067 ->
            let uu____5074 =
              let uu____5075 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____5075  in
            failwith uu____5074
        | FStar_Syntax_Syntax.Tm_uvar uu____5082 ->
            let uu____5099 =
              let uu____5100 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____5100  in
            failwith uu____5099
        | FStar_Syntax_Syntax.Tm_delayed uu____5107 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____5138 =
              let uu____5139 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____5139  in
            failwith uu____5138

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
      let uu____5163 =
        let uu____5164 = FStar_Syntax_Subst.compress e  in
        uu____5164.FStar_Syntax_Syntax.n  in
      match uu____5163 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5223;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5224;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5230 =
                  let uu___83_5231 = rc  in
                  let uu____5232 =
                    let uu____5237 =
                      let uu____5238 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____5238  in
                    FStar_Pervasives_Native.Some uu____5237  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___83_5231.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5232;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___83_5231.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____5230
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___84_5248 = env  in
            let uu____5249 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____5249;
              subst = (uu___84_5248.subst);
              tc_const = (uu___84_5248.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____5269  ->
                 match uu____5269 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___85_5282 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___85_5282.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___85_5282.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____5283 =
            FStar_List.fold_left
              (fun uu____5312  ->
                 fun uu____5313  ->
                   match (uu____5312, uu____5313) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____5361 = is_C c  in
                       if uu____5361
                       then
                         let xw =
                           let uu____5369 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5369
                            in
                         let x =
                           let uu___86_5371 = bv  in
                           let uu____5372 =
                             let uu____5375 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____5375  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___86_5371.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___86_5371.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5372
                           }  in
                         let env3 =
                           let uu___87_5377 = env2  in
                           let uu____5378 =
                             let uu____5381 =
                               let uu____5382 =
                                 let uu____5389 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____5389)  in
                               FStar_Syntax_Syntax.NT uu____5382  in
                             uu____5381 :: (env2.subst)  in
                           {
                             env = (uu___87_5377.env);
                             subst = uu____5378;
                             tc_const = (uu___87_5377.tc_const)
                           }  in
                         let uu____5390 =
                           let uu____5393 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____5394 =
                             let uu____5397 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____5397 :: acc  in
                           uu____5393 :: uu____5394  in
                         (env3, uu____5390)
                       else
                         (let x =
                            let uu___88_5402 = bv  in
                            let uu____5403 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___88_5402.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___88_5402.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5403
                            }  in
                          let uu____5406 =
                            let uu____5409 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____5409 :: acc  in
                          (env2, uu____5406))) (env1, []) binders1
             in
          (match uu____5283 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____5429 =
                 let check_what =
                   let uu____5447 = is_monadic rc_opt1  in
                   if uu____5447 then check_m else check_n  in
                 let uu____5459 = check_what env2 body1  in
                 match uu____5459 with
                 | (t,s_body,u_body) ->
                     let uu____5475 =
                       let uu____5476 =
                         let uu____5477 = is_monadic rc_opt1  in
                         if uu____5477 then M t else N t  in
                       comp_of_nm uu____5476  in
                     (uu____5475, s_body, u_body)
                  in
               (match uu____5429 with
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
                                 let uu____5502 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___69_5506  ->
                                           match uu___69_5506 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5507 -> false))
                                    in
                                 if uu____5502
                                 then
                                   let uu____5508 =
                                     FStar_List.filter
                                       (fun uu___70_5512  ->
                                          match uu___70_5512 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5513 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5508
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5522 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___71_5526  ->
                                         match uu___71_5526 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5527 -> false))
                                  in
                               if uu____5522
                               then
                                 let flags1 =
                                   FStar_List.filter
                                     (fun uu___72_5534  ->
                                        match uu___72_5534 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5535 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____5536 =
                                   let uu____5537 =
                                     let uu____5542 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____5542
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5537 flags1
                                    in
                                 FStar_Pervasives_Native.Some uu____5536
                               else
                                 (let uu____5544 =
                                    let uu___89_5545 = rc  in
                                    let uu____5546 =
                                      let uu____5551 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____5551
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___89_5545.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5546;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___89_5545.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____5544))
                       in
                    let uu____5552 =
                      let comp1 =
                        let uu____5562 = is_monadic rc_opt1  in
                        let uu____5563 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5562 uu____5563
                         in
                      let uu____5564 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____5564,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____5552 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____5606 =
                             let uu____5607 =
                               let uu____5624 =
                                 let uu____5627 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____5627 s_rc_opt  in
                               (s_binders1, s_body1, uu____5624)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5607  in
                           mk1 uu____5606  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____5637 =
                             let uu____5638 =
                               let uu____5655 =
                                 let uu____5658 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____5658 u_rc_opt  in
                               (u_binders2, u_body2, uu____5655)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5638  in
                           mk1 uu____5637  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5668;_};
            FStar_Syntax_Syntax.fv_delta = uu____5669;
            FStar_Syntax_Syntax.fv_qual = uu____5670;_}
          ->
          let uu____5673 =
            let uu____5678 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5678  in
          (match uu____5673 with
           | (uu____5709,t) ->
               let uu____5711 =
                 let uu____5712 = normalize1 t  in N uu____5712  in
               (uu____5711, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5713;
             FStar_Syntax_Syntax.vars = uu____5714;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5777 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5777 with
           | (unary_op,uu____5799) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5858;
             FStar_Syntax_Syntax.vars = uu____5859;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5935 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5935 with
           | (unary_op,uu____5957) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6022;
             FStar_Syntax_Syntax.vars = uu____6023;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____6061 = infer env a  in
          (match uu____6061 with
           | (t,s,u) ->
               let uu____6077 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6077 with
                | (head1,uu____6099) ->
                    let uu____6120 =
                      let uu____6121 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____6121  in
                    let uu____6122 =
                      let uu____6125 =
                        let uu____6126 =
                          let uu____6141 =
                            let uu____6144 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6144]  in
                          (head1, uu____6141)  in
                        FStar_Syntax_Syntax.Tm_app uu____6126  in
                      mk1 uu____6125  in
                    let uu____6149 =
                      let uu____6152 =
                        let uu____6153 =
                          let uu____6168 =
                            let uu____6171 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6171]  in
                          (head1, uu____6168)  in
                        FStar_Syntax_Syntax.Tm_app uu____6153  in
                      mk1 uu____6152  in
                    (uu____6120, uu____6122, uu____6149)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6180;
             FStar_Syntax_Syntax.vars = uu____6181;_},(a1,uu____6183)::a2::[])
          ->
          let uu____6225 = infer env a1  in
          (match uu____6225 with
           | (t,s,u) ->
               let uu____6241 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6241 with
                | (head1,uu____6263) ->
                    let uu____6284 =
                      let uu____6287 =
                        let uu____6288 =
                          let uu____6303 =
                            let uu____6306 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6306; a2]  in
                          (head1, uu____6303)  in
                        FStar_Syntax_Syntax.Tm_app uu____6288  in
                      mk1 uu____6287  in
                    let uu____6323 =
                      let uu____6326 =
                        let uu____6327 =
                          let uu____6342 =
                            let uu____6345 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6345; a2]  in
                          (head1, uu____6342)  in
                        FStar_Syntax_Syntax.Tm_app uu____6327  in
                      mk1 uu____6326  in
                    (t, uu____6284, uu____6323)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6366;
             FStar_Syntax_Syntax.vars = uu____6367;_},uu____6368)
          ->
          let uu____6389 =
            let uu____6394 =
              let uu____6395 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6395
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6394)  in
          FStar_Errors.raise_error uu____6389 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6402;
             FStar_Syntax_Syntax.vars = uu____6403;_},uu____6404)
          ->
          let uu____6425 =
            let uu____6430 =
              let uu____6431 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6431
               in
            (FStar_Errors.Fatal_IllAppliedConstant, uu____6430)  in
          FStar_Errors.raise_error uu____6425 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6460 = check_n env head1  in
          (match uu____6460 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6480 =
                   let uu____6481 = FStar_Syntax_Subst.compress t  in
                   uu____6481.FStar_Syntax_Syntax.n  in
                 match uu____6480 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6484 -> true
                 | uu____6497 -> false  in
               let rec flatten1 t =
                 let uu____6514 =
                   let uu____6515 = FStar_Syntax_Subst.compress t  in
                   uu____6515.FStar_Syntax_Syntax.n  in
                 match uu____6514 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6532);
                                FStar_Syntax_Syntax.pos = uu____6533;
                                FStar_Syntax_Syntax.vars = uu____6534;_})
                     when is_arrow t1 ->
                     let uu____6559 = flatten1 t1  in
                     (match uu____6559 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6641,uu____6642)
                     -> flatten1 e1
                 | uu____6683 ->
                     let uu____6684 =
                       let uu____6689 =
                         let uu____6690 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6690
                          in
                       (FStar_Errors.Fatal_NotFunctionType, uu____6689)  in
                     FStar_Errors.raise_err uu____6684
                  in
               let uu____6703 = flatten1 t_head  in
               (match uu____6703 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6763 =
                          let uu____6768 =
                            let uu____6769 = FStar_Util.string_of_int n1  in
                            let uu____6776 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____6787 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6769 uu____6776 uu____6787
                             in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu____6768)
                           in
                        FStar_Errors.raise_err uu____6763)
                     else ();
                     (let uu____6795 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____6795 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6836 args1 =
                            match uu____6836 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6910 =
                                       let uu____6911 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____6911.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____6910
                                 | (binders3,[]) ->
                                     let uu____6941 =
                                       let uu____6942 =
                                         let uu____6945 =
                                           let uu____6946 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6946
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____6945
                                          in
                                       uu____6942.FStar_Syntax_Syntax.n  in
                                     (match uu____6941 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6971 =
                                            let uu____6972 =
                                              let uu____6973 =
                                                let uu____6986 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____6986)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6973
                                               in
                                            mk1 uu____6972  in
                                          N uu____6971
                                      | uu____6993 -> failwith "wat?")
                                 | ([],uu____6994::uu____6995) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____7035)::binders3,(arg,uu____7038)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____7091 = FStar_List.splitAt n' binders1  in
                          (match uu____7091 with
                           | (binders2,uu____7123) ->
                               let uu____7148 =
                                 let uu____7169 =
                                   FStar_List.map2
                                     (fun uu____7223  ->
                                        fun uu____7224  ->
                                          match (uu____7223, uu____7224) with
                                          | ((bv,uu____7262),(arg,q)) ->
                                              let uu____7279 =
                                                let uu____7280 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____7280.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____7279 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7299 ->
                                                   let uu____7300 =
                                                     let uu____7305 =
                                                       star_type' env arg  in
                                                     (uu____7305, q)  in
                                                   (uu____7300, [(arg, q)])
                                               | uu____7332 ->
                                                   let uu____7333 =
                                                     check_n env arg  in
                                                   (match uu____7333 with
                                                    | (uu____7356,s_arg,u_arg)
                                                        ->
                                                        let uu____7359 =
                                                          let uu____7366 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____7366
                                                          then
                                                            let uu____7373 =
                                                              let uu____7378
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____7378, q)
                                                               in
                                                            [uu____7373;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____7359))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____7169  in
                               (match uu____7148 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____7477 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____7486 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____7477, uu____7486)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7554) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7560) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7566,uu____7567) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7609 = let uu____7610 = env.tc_const c  in N uu____7610
             in
          (uu____7609, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7611 ->
          let uu____7624 =
            let uu____7625 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7625  in
          failwith uu____7624
      | FStar_Syntax_Syntax.Tm_type uu____7632 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7639 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7658 ->
          let uu____7665 =
            let uu____7666 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7666  in
          failwith uu____7665
      | FStar_Syntax_Syntax.Tm_uvar uu____7673 ->
          let uu____7690 =
            let uu____7691 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7691  in
          failwith uu____7690
      | FStar_Syntax_Syntax.Tm_delayed uu____7698 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7729 =
            let uu____7730 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7730  in
          failwith uu____7729

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
          let uu____7775 = check_n env e0  in
          match uu____7775 with
          | (uu____7788,s_e0,u_e0) ->
              let uu____7791 =
                let uu____7820 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7881 = FStar_Syntax_Subst.open_branch b  in
                       match uu____7881 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___90_7923 = env  in
                             let uu____7924 =
                               let uu____7925 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7925
                                in
                             {
                               env = uu____7924;
                               subst = (uu___90_7923.subst);
                               tc_const = (uu___90_7923.tc_const)
                             }  in
                           let uu____7928 = f env1 body  in
                           (match uu____7928 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____8000 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____7820  in
              (match uu____7791 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____8102 = FStar_List.hd nms  in
                     match uu____8102 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___73_8108  ->
                          match uu___73_8108 with
                          | M uu____8109 -> true
                          | uu____8110 -> false) nms
                      in
                   let uu____8111 =
                     let uu____8148 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____8238  ->
                              match uu____8238 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8415 =
                                         check env original_body (M t2)  in
                                       (match uu____8415 with
                                        | (uu____8452,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8491,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____8148  in
                   (match uu____8111 with
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
                              (fun uu____8675  ->
                                 match uu____8675 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8726 =
                                         let uu____8727 =
                                           let uu____8742 =
                                             let uu____8749 =
                                               let uu____8754 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____8755 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____8754, uu____8755)  in
                                             [uu____8749]  in
                                           (s_body, uu____8742)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8727
                                          in
                                       mk1 uu____8726  in
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
                            let uu____8787 =
                              let uu____8788 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____8788]  in
                            let uu____8789 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____8787 uu____8789
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____8795 =
                              let uu____8802 =
                                let uu____8803 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8803
                                 in
                              [uu____8802]  in
                            let uu____8804 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____8795 uu____8804  in
                          let uu____8807 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____8846 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____8807, uu____8846)
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
                           let uu____8863 =
                             let uu____8866 =
                               let uu____8867 =
                                 let uu____8894 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____8894,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8867  in
                             mk1 uu____8866  in
                           let uu____8931 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____8863, uu____8931))))

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
              let uu____8978 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____8978]  in
            let uu____8979 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____8979 with
            | (x_binders1,e21) ->
                let uu____8992 = infer env e1  in
                (match uu____8992 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____9009 = is_C t1  in
                       if uu____9009
                       then
                         let uu___91_9010 = binding  in
                         let uu____9011 =
                           let uu____9014 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____9014  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___91_9010.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___91_9010.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____9011;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___91_9010.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___91_9010.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding  in
                     let env1 =
                       let uu___92_9017 = env  in
                       let uu____9018 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___93_9020 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___93_9020.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___93_9020.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9018;
                         subst = (uu___92_9017.subst);
                         tc_const = (uu___92_9017.tc_const)
                       }  in
                     let uu____9021 = proceed env1 e21  in
                     (match uu____9021 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___94_9038 = binding  in
                            let uu____9039 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___94_9038.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___94_9038.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____9039;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___94_9038.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___94_9038.FStar_Syntax_Syntax.lbdef)
                            }  in
                          let uu____9042 =
                            let uu____9045 =
                              let uu____9046 =
                                let uu____9059 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___95_9069 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___95_9069.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___95_9069.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___95_9069.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___95_9069.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____9059)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9046  in
                            mk1 uu____9045  in
                          let uu____9070 =
                            let uu____9073 =
                              let uu____9074 =
                                let uu____9087 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___96_9097 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___96_9097.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___96_9097.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___96_9097.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___96_9097.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____9087)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9074  in
                            mk1 uu____9073  in
                          (nm_rec, uu____9042, uu____9070))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___97_9106 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___97_9106.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___97_9106.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___97_9106.FStar_Syntax_Syntax.lbdef)
                       }  in
                     let env1 =
                       let uu___98_9108 = env  in
                       let uu____9109 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___99_9111 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___99_9111.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___99_9111.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____9109;
                         subst = (uu___98_9108.subst);
                         tc_const = (uu___98_9108.tc_const)
                       }  in
                     let uu____9112 = ensure_m env1 e21  in
                     (match uu____9112 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____9135 =
                              let uu____9136 =
                                let uu____9151 =
                                  let uu____9158 =
                                    let uu____9163 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____9164 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9163, uu____9164)  in
                                  [uu____9158]  in
                                (s_e2, uu____9151)  in
                              FStar_Syntax_Syntax.Tm_app uu____9136  in
                            mk1 uu____9135  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____9183 =
                              let uu____9184 =
                                let uu____9199 =
                                  let uu____9206 =
                                    let uu____9211 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____9211)  in
                                  [uu____9206]  in
                                (s_e1, uu____9199)  in
                              FStar_Syntax_Syntax.Tm_app uu____9184  in
                            mk1 uu____9183  in
                          let uu____9226 =
                            let uu____9227 =
                              let uu____9228 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____9228]  in
                            FStar_Syntax_Util.abs uu____9227 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____9229 =
                            let uu____9232 =
                              let uu____9233 =
                                let uu____9246 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___100_9256 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___100_9256.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___100_9256.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___100_9256.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___100_9256.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____9246)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____9233  in
                            mk1 uu____9232  in
                          ((M t2), uu____9226, uu____9229)))

and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9268 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____9268  in
      let uu____9269 = check env e mn  in
      match uu____9269 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9285 -> failwith "[check_n]: impossible"

and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9307 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____9307  in
      let uu____9308 = check env e mn  in
      match uu____9308 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9324 -> failwith "[check_m]: impossible"

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
        (let uu____9354 =
           let uu____9355 = is_C c  in Prims.op_Negation uu____9355  in
         if uu____9354 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____9363 =
           let uu____9364 = FStar_Syntax_Subst.compress c  in
           uu____9364.FStar_Syntax_Syntax.n  in
         match uu____9363 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9389 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____9389 with
              | (wp_head,wp_args) ->
                  ((let uu____9427 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9441 =
                           let uu____9442 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9442
                            in
                         Prims.op_Negation uu____9441)
                       in
                    if uu____9427 then failwith "mismatch" else ());
                   (let uu____9450 =
                      let uu____9451 =
                        let uu____9466 =
                          FStar_List.map2
                            (fun uu____9494  ->
                               fun uu____9495  ->
                                 match (uu____9494, uu____9495) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9532 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____9532
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____9535 =
                                           let uu____9540 =
                                             let uu____9541 =
                                               print_implicit q  in
                                             let uu____9542 =
                                               print_implicit q'  in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %b %b\n"
                                               uu____9541 uu____9542
                                              in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu____9540)
                                            in
                                         FStar_Errors.log_issue
                                           head1.FStar_Syntax_Syntax.pos
                                           uu____9535)
                                      else ();
                                      (let uu____9544 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____9544, q)))) args wp_args
                           in
                        (head1, uu____9466)  in
                      FStar_Syntax_Syntax.Tm_app uu____9451  in
                    mk1 uu____9450)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____9578 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____9578 with
              | (binders_orig,comp1) ->
                  let uu____9585 =
                    let uu____9600 =
                      FStar_List.map
                        (fun uu____9634  ->
                           match uu____9634 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____9654 = is_C h  in
                               if uu____9654
                               then
                                 let w' =
                                   let uu____9666 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9666
                                    in
                                 let uu____9667 =
                                   let uu____9674 =
                                     let uu____9681 =
                                       let uu____9686 =
                                         let uu____9687 =
                                           let uu____9688 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____9688  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9687
                                          in
                                       (uu____9686, q)  in
                                     [uu____9681]  in
                                   (w', q) :: uu____9674  in
                                 (w', uu____9667)
                               else
                                 (let x =
                                    let uu____9709 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9709
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____9600  in
                  (match uu____9585 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____9764 =
                           let uu____9767 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9767
                            in
                         FStar_Syntax_Subst.subst_comp uu____9764 comp1  in
                       let app =
                         let uu____9771 =
                           let uu____9772 =
                             let uu____9787 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9802 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____9803 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9802, uu____9803)) bvs
                                in
                             (wp, uu____9787)  in
                           FStar_Syntax_Syntax.Tm_app uu____9772  in
                         mk1 uu____9771  in
                       let comp3 =
                         let uu____9811 = type_of_comp comp2  in
                         let uu____9812 = is_monadic_comp comp2  in
                         trans_G env uu____9811 uu____9812 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9814,uu____9815) ->
             trans_F_ env e wp
         | uu____9856 -> failwith "impossible trans_F_")

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
            let uu____9861 =
              let uu____9862 = star_type' env h  in
              let uu____9865 =
                let uu____9874 =
                  let uu____9879 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____9879)  in
                [uu____9874]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9862;
                FStar_Syntax_Syntax.effect_args = uu____9865;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____9861
          else
            (let uu____9889 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____9889)

let (n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.NoDeltaSteps;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
  
let (star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun env  ->
    fun t  -> let uu____9900 = n env.env t  in star_type' env uu____9900
  
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun t  -> let uu____9915 = n env.env t  in check_n env uu____9915
  
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____9925 = n env.env c  in
        let uu____9926 = n env.env wp  in trans_F_ env uu____9925 uu____9926
  