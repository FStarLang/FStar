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
              let uu___297_93 = a  in
              let uu____94 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Normalize.EraseUniverses] env
                  a.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___297_93.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___297_93.FStar_Syntax_Syntax.index);
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
                  (fun uu____418  ->
                     match uu____418 with
                     | (t,b) ->
                         let uu____429 = FStar_Syntax_Syntax.as_implicit b
                            in
                         (t, uu____429))
                 in
              let mk_all_implicit =
                FStar_List.map
                  (fun t  ->
                     let uu____460 = FStar_Syntax_Syntax.as_implicit true  in
                     ((FStar_Pervasives_Native.fst t), uu____460))
                 in
              let args_of_binders1 =
                FStar_List.map
                  (fun bv  ->
                     let uu____483 =
                       FStar_Syntax_Syntax.bv_to_name
                         (FStar_Pervasives_Native.fst bv)
                        in
                     FStar_Syntax_Syntax.as_arg uu____483)
                 in
              let uu____484 =
                let uu____499 =
                  let mk2 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let body =
                      let uu____521 = f (FStar_Syntax_Syntax.bv_to_name t)
                         in
                      FStar_Syntax_Util.arrow gamma uu____521  in
                    let uu____524 =
                      let uu____525 =
                        let uu____532 = FStar_Syntax_Syntax.mk_binder a1  in
                        let uu____533 =
                          let uu____536 = FStar_Syntax_Syntax.mk_binder t  in
                          [uu____536]  in
                        uu____532 :: uu____533  in
                      FStar_List.append binders uu____525  in
                    FStar_Syntax_Util.abs uu____524 body
                      FStar_Pervasives_Native.None
                     in
                  let uu____541 = mk2 FStar_Syntax_Syntax.mk_Total  in
                  let uu____542 = mk2 FStar_Syntax_Syntax.mk_GTotal  in
                  (uu____541, uu____542)  in
                match uu____499 with
                | (ctx_def,gctx_def) ->
                    let ctx_lid = mk_lid "ctx"  in
                    let ctx_fv = register env ctx_lid ctx_def  in
                    let gctx_lid = mk_lid "gctx"  in
                    let gctx_fv = register env gctx_lid gctx_def  in
                    let mk_app1 fv t =
                      let uu____576 =
                        let uu____577 =
                          let uu____592 =
                            let uu____599 =
                              FStar_List.map
                                (fun uu____619  ->
                                   match uu____619 with
                                   | (bv,uu____629) ->
                                       let uu____630 =
                                         FStar_Syntax_Syntax.bv_to_name bv
                                          in
                                       let uu____631 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false
                                          in
                                       (uu____630, uu____631)) binders
                               in
                            let uu____632 =
                              let uu____639 =
                                let uu____644 =
                                  FStar_Syntax_Syntax.bv_to_name a1  in
                                let uu____645 =
                                  FStar_Syntax_Syntax.as_implicit false  in
                                (uu____644, uu____645)  in
                              let uu____646 =
                                let uu____653 =
                                  let uu____658 =
                                    FStar_Syntax_Syntax.as_implicit false  in
                                  (t, uu____658)  in
                                [uu____653]  in
                              uu____639 :: uu____646  in
                            FStar_List.append uu____599 uu____632  in
                          (fv, uu____592)  in
                        FStar_Syntax_Syntax.Tm_app uu____577  in
                      mk1 uu____576  in
                    (env, (mk_app1 ctx_fv), (mk_app1 gctx_fv))
                 in
              match uu____484 with
              | (env1,mk_ctx,mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let x =
                      let uu____717 = FStar_Syntax_Syntax.bv_to_name t  in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu____717
                       in
                    let ret1 =
                      let uu____721 =
                        let uu____722 =
                          let uu____725 = FStar_Syntax_Syntax.bv_to_name t
                             in
                          mk_ctx uu____725  in
                        FStar_Syntax_Util.residual_tot uu____722  in
                      FStar_Pervasives_Native.Some uu____721  in
                    let body =
                      let uu____727 = FStar_Syntax_Syntax.bv_to_name x  in
                      FStar_Syntax_Util.abs gamma uu____727 ret1  in
                    let uu____728 =
                      let uu____729 = mk_all_implicit binders  in
                      let uu____736 =
                        binders_of_list1 [(a1, true); (t, true); (x, false)]
                         in
                      FStar_List.append uu____729 uu____736  in
                    FStar_Syntax_Util.abs uu____728 body ret1  in
                  let c_pure1 =
                    let uu____764 = mk_lid "pure"  in
                    register env1 uu____764 c_pure  in
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
                      let uu____769 =
                        let uu____770 =
                          let uu____771 =
                            let uu____778 =
                              let uu____779 =
                                let uu____780 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu____780
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____779  in
                            [uu____778]  in
                          let uu____781 =
                            let uu____784 = FStar_Syntax_Syntax.bv_to_name t2
                               in
                            FStar_Syntax_Syntax.mk_GTotal uu____784  in
                          FStar_Syntax_Util.arrow uu____771 uu____781  in
                        mk_gctx uu____770  in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu____769
                       in
                    let r =
                      let uu____786 =
                        let uu____787 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____787  in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu____786
                       in
                    let ret1 =
                      let uu____791 =
                        let uu____792 =
                          let uu____795 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____795  in
                        FStar_Syntax_Util.residual_tot uu____792  in
                      FStar_Pervasives_Native.Some uu____791  in
                    let outer_body =
                      let gamma_as_args = args_of_binders1 gamma  in
                      let inner_body =
                        let uu____803 = FStar_Syntax_Syntax.bv_to_name l  in
                        let uu____806 =
                          let uu____815 =
                            let uu____818 =
                              let uu____819 =
                                let uu____820 =
                                  FStar_Syntax_Syntax.bv_to_name r  in
                                FStar_Syntax_Util.mk_app uu____820
                                  gamma_as_args
                                 in
                              FStar_Syntax_Syntax.as_arg uu____819  in
                            [uu____818]  in
                          FStar_List.append gamma_as_args uu____815  in
                        FStar_Syntax_Util.mk_app uu____803 uu____806  in
                      FStar_Syntax_Util.abs gamma inner_body ret1  in
                    let uu____823 =
                      let uu____824 = mk_all_implicit binders  in
                      let uu____831 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)]
                         in
                      FStar_List.append uu____824 uu____831  in
                    FStar_Syntax_Util.abs uu____823 outer_body ret1  in
                  let c_app1 =
                    let uu____867 = mk_lid "app"  in
                    register env1 uu____867 c_app  in
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
                      let uu____874 =
                        let uu____881 =
                          let uu____882 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____882  in
                        [uu____881]  in
                      let uu____883 =
                        let uu____886 = FStar_Syntax_Syntax.bv_to_name t2  in
                        FStar_Syntax_Syntax.mk_GTotal uu____886  in
                      FStar_Syntax_Util.arrow uu____874 uu____883  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____889 =
                        let uu____890 = FStar_Syntax_Syntax.bv_to_name t1  in
                        mk_gctx uu____890  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____889
                       in
                    let ret1 =
                      let uu____894 =
                        let uu____895 =
                          let uu____898 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____898  in
                        FStar_Syntax_Util.residual_tot uu____895  in
                      FStar_Pervasives_Native.Some uu____894  in
                    let uu____899 =
                      let uu____900 = mk_all_implicit binders  in
                      let uu____907 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)]
                         in
                      FStar_List.append uu____900 uu____907  in
                    let uu____942 =
                      let uu____943 =
                        let uu____952 =
                          let uu____955 =
                            let uu____958 =
                              let uu____967 =
                                let uu____970 =
                                  FStar_Syntax_Syntax.bv_to_name f  in
                                [uu____970]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____967
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____958  in
                          let uu____971 =
                            let uu____976 =
                              FStar_Syntax_Syntax.bv_to_name a11  in
                            [uu____976]  in
                          uu____955 :: uu____971  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____952
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____943  in
                    FStar_Syntax_Util.abs uu____899 uu____942 ret1  in
                  let c_lift11 =
                    let uu____980 = mk_lid "lift1"  in
                    register env1 uu____980 c_lift1  in
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
                      let uu____988 =
                        let uu____995 =
                          let uu____996 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____996  in
                        let uu____997 =
                          let uu____1000 =
                            let uu____1001 =
                              FStar_Syntax_Syntax.bv_to_name t2  in
                            FStar_Syntax_Syntax.null_binder uu____1001  in
                          [uu____1000]  in
                        uu____995 :: uu____997  in
                      let uu____1002 =
                        let uu____1005 = FStar_Syntax_Syntax.bv_to_name t3
                           in
                        FStar_Syntax_Syntax.mk_GTotal uu____1005  in
                      FStar_Syntax_Util.arrow uu____988 uu____1002  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let a11 =
                      let uu____1008 =
                        let uu____1009 = FStar_Syntax_Syntax.bv_to_name t1
                           in
                        mk_gctx uu____1009  in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu____1008
                       in
                    let a2 =
                      let uu____1011 =
                        let uu____1012 = FStar_Syntax_Syntax.bv_to_name t2
                           in
                        mk_gctx uu____1012  in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu____1011
                       in
                    let ret1 =
                      let uu____1016 =
                        let uu____1017 =
                          let uu____1020 = FStar_Syntax_Syntax.bv_to_name t3
                             in
                          mk_gctx uu____1020  in
                        FStar_Syntax_Util.residual_tot uu____1017  in
                      FStar_Pervasives_Native.Some uu____1016  in
                    let uu____1021 =
                      let uu____1022 = mk_all_implicit binders  in
                      let uu____1029 =
                        binders_of_list1
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)]
                         in
                      FStar_List.append uu____1022 uu____1029  in
                    let uu____1072 =
                      let uu____1073 =
                        let uu____1082 =
                          let uu____1085 =
                            let uu____1088 =
                              let uu____1097 =
                                let uu____1100 =
                                  let uu____1103 =
                                    let uu____1112 =
                                      let uu____1115 =
                                        FStar_Syntax_Syntax.bv_to_name f  in
                                      [uu____1115]  in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu____1112
                                     in
                                  FStar_Syntax_Util.mk_app c_pure1 uu____1103
                                   in
                                let uu____1116 =
                                  let uu____1121 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  [uu____1121]  in
                                uu____1100 :: uu____1116  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1097
                               in
                            FStar_Syntax_Util.mk_app c_app1 uu____1088  in
                          let uu____1124 =
                            let uu____1129 =
                              FStar_Syntax_Syntax.bv_to_name a2  in
                            [uu____1129]  in
                          uu____1085 :: uu____1124  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1082
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1073  in
                    FStar_Syntax_Util.abs uu____1021 uu____1072 ret1  in
                  let c_lift21 =
                    let uu____1133 = mk_lid "lift2"  in
                    register env1 uu____1133 c_lift2  in
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
                      let uu____1140 =
                        let uu____1147 =
                          let uu____1148 = FStar_Syntax_Syntax.bv_to_name t1
                             in
                          FStar_Syntax_Syntax.null_binder uu____1148  in
                        [uu____1147]  in
                      let uu____1149 =
                        let uu____1152 =
                          let uu____1153 = FStar_Syntax_Syntax.bv_to_name t2
                             in
                          mk_gctx uu____1153  in
                        FStar_Syntax_Syntax.mk_Total uu____1152  in
                      FStar_Syntax_Util.arrow uu____1140 uu____1149  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let ret1 =
                      let uu____1158 =
                        let uu____1159 =
                          let uu____1162 =
                            let uu____1163 =
                              let uu____1170 =
                                let uu____1171 =
                                  FStar_Syntax_Syntax.bv_to_name t1  in
                                FStar_Syntax_Syntax.null_binder uu____1171
                                 in
                              [uu____1170]  in
                            let uu____1172 =
                              let uu____1175 =
                                FStar_Syntax_Syntax.bv_to_name t2  in
                              FStar_Syntax_Syntax.mk_GTotal uu____1175  in
                            FStar_Syntax_Util.arrow uu____1163 uu____1172  in
                          mk_ctx uu____1162  in
                        FStar_Syntax_Util.residual_tot uu____1159  in
                      FStar_Pervasives_Native.Some uu____1158  in
                    let e1 =
                      let uu____1177 = FStar_Syntax_Syntax.bv_to_name t1  in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu____1177
                       in
                    let body =
                      let uu____1179 =
                        let uu____1180 =
                          let uu____1187 = FStar_Syntax_Syntax.mk_binder e1
                             in
                          [uu____1187]  in
                        FStar_List.append gamma uu____1180  in
                      let uu____1192 =
                        let uu____1193 = FStar_Syntax_Syntax.bv_to_name f  in
                        let uu____1196 =
                          let uu____1205 =
                            let uu____1206 =
                              FStar_Syntax_Syntax.bv_to_name e1  in
                            FStar_Syntax_Syntax.as_arg uu____1206  in
                          let uu____1207 = args_of_binders1 gamma  in
                          uu____1205 :: uu____1207  in
                        FStar_Syntax_Util.mk_app uu____1193 uu____1196  in
                      FStar_Syntax_Util.abs uu____1179 uu____1192 ret1  in
                    let uu____1210 =
                      let uu____1211 = mk_all_implicit binders  in
                      let uu____1218 =
                        binders_of_list1
                          [(a1, true); (t1, true); (t2, true); (f, false)]
                         in
                      FStar_List.append uu____1211 uu____1218  in
                    FStar_Syntax_Util.abs uu____1210 body ret1  in
                  let c_push1 =
                    let uu____1250 = mk_lid "push"  in
                    register env1 uu____1250 c_push  in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1)
                     in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > (Prims.parse_int "0")
                    then
                      let uu____1270 =
                        let uu____1271 =
                          let uu____1286 = args_of_binders1 binders  in
                          (c, uu____1286)  in
                        FStar_Syntax_Syntax.Tm_app uu____1271  in
                      mk1 uu____1270
                    else c  in
                  let wp_if_then_else =
                    let result_comp =
                      let uu____1296 =
                        let uu____1297 =
                          let uu____1304 =
                            FStar_Syntax_Syntax.null_binder wp_a1  in
                          let uu____1305 =
                            let uu____1308 =
                              FStar_Syntax_Syntax.null_binder wp_a1  in
                            [uu____1308]  in
                          uu____1304 :: uu____1305  in
                        let uu____1309 = FStar_Syntax_Syntax.mk_Total wp_a1
                           in
                        FStar_Syntax_Util.arrow uu____1297 uu____1309  in
                      FStar_Syntax_Syntax.mk_Total uu____1296  in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let uu____1313 =
                      let uu____1314 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c]  in
                      FStar_List.append binders uu____1314  in
                    let uu____1325 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_defined_at_level
                             (Prims.parse_int "2"))
                          FStar_Pervasives_Native.None
                         in
                      let uu____1327 =
                        let uu____1330 =
                          let uu____1339 =
                            let uu____1342 =
                              let uu____1345 =
                                let uu____1354 =
                                  let uu____1355 =
                                    FStar_Syntax_Syntax.bv_to_name c  in
                                  FStar_Syntax_Syntax.as_arg uu____1355  in
                                [uu____1354]  in
                              FStar_Syntax_Util.mk_app l_ite uu____1345  in
                            [uu____1342]  in
                          FStar_List.map FStar_Syntax_Syntax.as_arg
                            uu____1339
                           in
                        FStar_Syntax_Util.mk_app c_lift21 uu____1330  in
                      FStar_Syntax_Util.ascribe uu____1327
                        ((FStar_Util.Inr result_comp),
                          FStar_Pervasives_Native.None)
                       in
                    FStar_Syntax_Util.abs uu____1313 uu____1325
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp))
                     in
                  let wp_if_then_else1 =
                    let uu____1375 = mk_lid "wp_if_then_else"  in
                    register env1 uu____1375 wp_if_then_else  in
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
                      let uu____1386 =
                        let uu____1395 =
                          let uu____1398 =
                            let uu____1401 =
                              let uu____1410 =
                                let uu____1413 =
                                  let uu____1416 =
                                    let uu____1425 =
                                      let uu____1426 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1426
                                       in
                                    [uu____1425]  in
                                  FStar_Syntax_Util.mk_app l_and uu____1416
                                   in
                                [uu____1413]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1410
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1401  in
                          let uu____1431 =
                            let uu____1436 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1436]  in
                          uu____1398 :: uu____1431  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1395
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1386  in
                    let uu____1439 =
                      let uu____1440 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1440  in
                    FStar_Syntax_Util.abs uu____1439 body ret_tot_wp_a  in
                  let wp_assert1 =
                    let uu____1452 = mk_lid "wp_assert"  in
                    register env1 uu____1452 wp_assert  in
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
                      let uu____1463 =
                        let uu____1472 =
                          let uu____1475 =
                            let uu____1478 =
                              let uu____1487 =
                                let uu____1490 =
                                  let uu____1493 =
                                    let uu____1502 =
                                      let uu____1503 =
                                        FStar_Syntax_Syntax.bv_to_name q  in
                                      FStar_Syntax_Syntax.as_arg uu____1503
                                       in
                                    [uu____1502]  in
                                  FStar_Syntax_Util.mk_app l_imp uu____1493
                                   in
                                [uu____1490]  in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu____1487
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1478  in
                          let uu____1508 =
                            let uu____1513 =
                              FStar_Syntax_Syntax.bv_to_name wp  in
                            [uu____1513]  in
                          uu____1475 :: uu____1508  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1472
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1463  in
                    let uu____1516 =
                      let uu____1517 =
                        FStar_Syntax_Syntax.binders_of_list [a1; q; wp]  in
                      FStar_List.append binders uu____1517  in
                    FStar_Syntax_Util.abs uu____1516 body ret_tot_wp_a  in
                  let wp_assume1 =
                    let uu____1529 = mk_lid "wp_assume"  in
                    register env1 uu____1529 wp_assume  in
                  let wp_assume2 = mk_generic_app wp_assume1  in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype
                       in
                    let t_f =
                      let uu____1538 =
                        let uu____1545 =
                          let uu____1546 = FStar_Syntax_Syntax.bv_to_name b
                             in
                          FStar_Syntax_Syntax.null_binder uu____1546  in
                        [uu____1545]  in
                      let uu____1547 = FStar_Syntax_Syntax.mk_Total wp_a1  in
                      FStar_Syntax_Util.arrow uu____1538 uu____1547  in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f
                       in
                    let body =
                      let uu____1554 =
                        let uu____1563 =
                          let uu____1566 =
                            let uu____1569 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall]
                               in
                            FStar_Syntax_Util.mk_app c_pure1 uu____1569  in
                          let uu____1578 =
                            let uu____1583 =
                              let uu____1586 =
                                let uu____1595 =
                                  let uu____1598 =
                                    FStar_Syntax_Syntax.bv_to_name f  in
                                  [uu____1598]  in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu____1595
                                 in
                              FStar_Syntax_Util.mk_app c_push1 uu____1586  in
                            [uu____1583]  in
                          uu____1566 :: uu____1578  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____1563
                         in
                      FStar_Syntax_Util.mk_app c_app1 uu____1554  in
                    let uu____1605 =
                      let uu____1606 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f]  in
                      FStar_List.append binders uu____1606  in
                    FStar_Syntax_Util.abs uu____1605 body ret_tot_wp_a  in
                  let wp_close1 =
                    let uu____1618 = mk_lid "wp_close"  in
                    register env1 uu____1618 wp_close  in
                  let wp_close2 = mk_generic_app wp_close1  in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype)
                     in
                  let ret_gtot_type =
                    let uu____1628 =
                      let uu____1629 =
                        let uu____1630 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype
                           in
                        FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                          uu____1630
                         in
                      FStar_Syntax_Util.residual_comp_of_lcomp uu____1629  in
                    FStar_Pervasives_Native.Some uu____1628  in
                  let mk_forall1 x body =
                    let uu____1642 =
                      let uu____1645 =
                        let uu____1646 =
                          let uu____1661 =
                            let uu____1664 =
                              let uu____1665 =
                                let uu____1666 =
                                  let uu____1667 =
                                    FStar_Syntax_Syntax.mk_binder x  in
                                  [uu____1667]  in
                                FStar_Syntax_Util.abs uu____1666 body
                                  ret_tot_type
                                 in
                              FStar_Syntax_Syntax.as_arg uu____1665  in
                            [uu____1664]  in
                          (FStar_Syntax_Util.tforall, uu____1661)  in
                        FStar_Syntax_Syntax.Tm_app uu____1646  in
                      FStar_Syntax_Syntax.mk uu____1645  in
                    uu____1642 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let rec is_discrete t =
                    let uu____1677 =
                      let uu____1678 = FStar_Syntax_Subst.compress t  in
                      uu____1678.FStar_Syntax_Syntax.n  in
                    match uu____1677 with
                    | FStar_Syntax_Syntax.Tm_type uu____1681 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1707  ->
                              match uu____1707 with
                              | (b,uu____1713) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu____1714 -> true  in
                  let rec is_monotonic t =
                    let uu____1719 =
                      let uu____1720 = FStar_Syntax_Subst.compress t  in
                      uu____1720.FStar_Syntax_Syntax.n  in
                    match uu____1719 with
                    | FStar_Syntax_Syntax.Tm_type uu____1723 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                        (FStar_List.for_all
                           (fun uu____1749  ->
                              match uu____1749 with
                              | (b,uu____1755) ->
                                  is_discrete b.FStar_Syntax_Syntax.sort) bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu____1756 -> is_discrete t  in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel  in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.Beta;
                        FStar_TypeChecker_Normalize.Eager_unfolding;
                        FStar_TypeChecker_Normalize.UnfoldUntil
                          FStar_Syntax_Syntax.Delta_constant] env1 t
                       in
                    let uu____1808 =
                      let uu____1809 = FStar_Syntax_Subst.compress t1  in
                      uu____1809.FStar_Syntax_Syntax.n  in
                    match uu____1808 with
                    | FStar_Syntax_Syntax.Tm_type uu____1812 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____1815);
                                      FStar_Syntax_Syntax.pos = uu____1816;
                                      FStar_Syntax_Syntax.vars = uu____1817;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1851 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1851
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____1854 =
                              let uu____1857 =
                                let uu____1866 =
                                  let uu____1867 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1867  in
                                [uu____1866]  in
                              FStar_Syntax_Util.mk_app x uu____1857  in
                            let uu____1868 =
                              let uu____1871 =
                                let uu____1880 =
                                  let uu____1881 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1881  in
                                [uu____1880]  in
                              FStar_Syntax_Util.mk_app y uu____1871  in
                            mk_rel1 b uu____1854 uu____1868  in
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
                             let uu____1886 =
                               let uu____1887 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____1890 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1887 uu____1890  in
                             let uu____1893 =
                               let uu____1894 =
                                 let uu____1897 =
                                   let uu____1906 =
                                     let uu____1907 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____1907
                                      in
                                   [uu____1906]  in
                                 FStar_Syntax_Util.mk_app x uu____1897  in
                               let uu____1908 =
                                 let uu____1911 =
                                   let uu____1920 =
                                     let uu____1921 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____1921
                                      in
                                   [uu____1920]  in
                                 FStar_Syntax_Util.mk_app y uu____1911  in
                               mk_rel1 b uu____1894 uu____1908  in
                             FStar_Syntax_Util.mk_imp uu____1886 uu____1893
                              in
                           let uu____1922 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____1922)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____1925);
                                      FStar_Syntax_Syntax.pos = uu____1926;
                                      FStar_Syntax_Syntax.vars = uu____1927;_})
                        ->
                        let a2 =
                          (FStar_Pervasives_Native.fst binder).FStar_Syntax_Syntax.sort
                           in
                        let uu____1961 =
                          (is_monotonic a2) || (is_monotonic b)  in
                        if uu____1961
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2
                             in
                          let body =
                            let uu____1964 =
                              let uu____1967 =
                                let uu____1976 =
                                  let uu____1977 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1977  in
                                [uu____1976]  in
                              FStar_Syntax_Util.mk_app x uu____1967  in
                            let uu____1978 =
                              let uu____1981 =
                                let uu____1990 =
                                  let uu____1991 =
                                    FStar_Syntax_Syntax.bv_to_name a11  in
                                  FStar_Syntax_Syntax.as_arg uu____1991  in
                                [uu____1990]  in
                              FStar_Syntax_Util.mk_app y uu____1981  in
                            mk_rel1 b uu____1964 uu____1978  in
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
                             let uu____1996 =
                               let uu____1997 =
                                 FStar_Syntax_Syntax.bv_to_name a11  in
                               let uu____2000 =
                                 FStar_Syntax_Syntax.bv_to_name a21  in
                               mk_rel1 a2 uu____1997 uu____2000  in
                             let uu____2003 =
                               let uu____2004 =
                                 let uu____2007 =
                                   let uu____2016 =
                                     let uu____2017 =
                                       FStar_Syntax_Syntax.bv_to_name a11  in
                                     FStar_Syntax_Syntax.as_arg uu____2017
                                      in
                                   [uu____2016]  in
                                 FStar_Syntax_Util.mk_app x uu____2007  in
                               let uu____2018 =
                                 let uu____2021 =
                                   let uu____2030 =
                                     let uu____2031 =
                                       FStar_Syntax_Syntax.bv_to_name a21  in
                                     FStar_Syntax_Syntax.as_arg uu____2031
                                      in
                                   [uu____2030]  in
                                 FStar_Syntax_Util.mk_app y uu____2021  in
                               mk_rel1 b uu____2004 uu____2018  in
                             FStar_Syntax_Util.mk_imp uu____1996 uu____2003
                              in
                           let uu____2032 = mk_forall1 a21 body  in
                           mk_forall1 a11 uu____2032)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1,comp) ->
                        let t2 =
                          let uu___298_2063 = t1  in
                          let uu____2064 =
                            let uu____2065 =
                              let uu____2078 =
                                let uu____2079 =
                                  FStar_Syntax_Util.arrow binders1 comp  in
                                FStar_Syntax_Syntax.mk_Total uu____2079  in
                              ([binder], uu____2078)  in
                            FStar_Syntax_Syntax.Tm_arrow uu____2065  in
                          {
                            FStar_Syntax_Syntax.n = uu____2064;
                            FStar_Syntax_Syntax.pos =
                              (uu___298_2063.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___298_2063.FStar_Syntax_Syntax.vars)
                          }  in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow uu____2094 ->
                        failwith "unhandled arrow"
                    | uu____2107 -> FStar_Syntax_Util.mk_untyped_eq2 x y  in
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
                      let uu____2122 =
                        let uu____2123 = FStar_Syntax_Subst.compress t1  in
                        uu____2123.FStar_Syntax_Syntax.n  in
                      match uu____2122 with
                      | FStar_Syntax_Syntax.Tm_type uu____2126 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head1,args) when
                          let uu____2149 = FStar_Syntax_Subst.compress head1
                             in
                          FStar_Syntax_Util.is_tuple_constructor uu____2149
                          ->
                          let project i tuple =
                            let projector =
                              let uu____2164 =
                                let uu____2165 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange
                                   in
                                FStar_TypeChecker_Env.lookup_projector env1
                                  uu____2165 i
                                 in
                              FStar_Syntax_Syntax.fvar uu____2164
                                (FStar_Syntax_Syntax.Delta_defined_at_level
                                   (Prims.parse_int "1"))
                                FStar_Pervasives_Native.None
                               in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)]
                             in
                          let uu____2192 =
                            let uu____2199 =
                              FStar_List.mapi
                                (fun i  ->
                                   fun uu____2213  ->
                                     match uu____2213 with
                                     | (t2,q) ->
                                         let uu____2220 = project i x  in
                                         let uu____2221 = project i y  in
                                         mk_stronger t2 uu____2220 uu____2221)
                                args
                               in
                            match uu____2199 with
                            | [] ->
                                failwith
                                  "Impossible : Empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels)  in
                          (match uu____2192 with
                           | (rel0,rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.GTotal
                                        (b,uu____2248);
                                      FStar_Syntax_Syntax.pos = uu____2249;
                                      FStar_Syntax_Syntax.vars = uu____2250;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2288  ->
                                   match uu____2288 with
                                   | (bv,q) ->
                                       let uu____2295 =
                                         let uu____2296 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2296  in
                                       FStar_Syntax_Syntax.gen_bv uu____2295
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2303 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2303) bvs
                             in
                          let body =
                            let uu____2305 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2306 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2305 uu____2306  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Total
                                        (b,uu____2313);
                                      FStar_Syntax_Syntax.pos = uu____2314;
                                      FStar_Syntax_Syntax.vars = uu____2315;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i  ->
                                 fun uu____2353  ->
                                   match uu____2353 with
                                   | (bv,q) ->
                                       let uu____2360 =
                                         let uu____2361 =
                                           FStar_Util.string_of_int i  in
                                         Prims.strcat "a" uu____2361  in
                                       FStar_Syntax_Syntax.gen_bv uu____2360
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1
                             in
                          let args =
                            FStar_List.map
                              (fun ai  ->
                                 let uu____2368 =
                                   FStar_Syntax_Syntax.bv_to_name ai  in
                                 FStar_Syntax_Syntax.as_arg uu____2368) bvs
                             in
                          let body =
                            let uu____2370 = FStar_Syntax_Util.mk_app x args
                               in
                            let uu____2371 = FStar_Syntax_Util.mk_app y args
                               in
                            mk_stronger b uu____2370 uu____2371  in
                          FStar_List.fold_right
                            (fun bv  -> fun body1  -> mk_forall1 bv body1)
                            bvs body
                      | uu____2376 -> failwith "Not a DM elaborated type"  in
                    let body =
                      let uu____2378 = FStar_Syntax_Util.unascribe wp_a1  in
                      let uu____2379 = FStar_Syntax_Syntax.bv_to_name wp1  in
                      let uu____2380 = FStar_Syntax_Syntax.bv_to_name wp2  in
                      mk_stronger uu____2378 uu____2379 uu____2380  in
                    let uu____2381 =
                      let uu____2382 =
                        binders_of_list1
                          [(a1, false); (wp1, false); (wp2, false)]
                         in
                      FStar_List.append binders uu____2382  in
                    FStar_Syntax_Util.abs uu____2381 body ret_tot_type  in
                  let stronger1 =
                    let uu____2410 = mk_lid "stronger"  in
                    register env1 uu____2410 stronger  in
                  let stronger2 = mk_generic_app stronger1  in
                  let wp_ite =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2416 = FStar_Util.prefix gamma  in
                    match uu____2416 with
                    | (wp_args,post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (FStar_Pervasives_Native.fst post).FStar_Syntax_Syntax.sort
                           in
                        let equiv1 =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k  in
                          let eq1 =
                            let uu____2461 =
                              FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu____2461
                             in
                          let uu____2464 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq1  in
                          match uu____2464 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1,[],body)) ->
                              let k_app =
                                let uu____2474 = args_of_binders1 binders1
                                   in
                                FStar_Syntax_Util.mk_app k_tm uu____2474  in
                              let guard_free1 =
                                let uu____2484 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.Delta_constant
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.fv_to_tm uu____2484  in
                              let pat =
                                let uu____2488 =
                                  let uu____2497 =
                                    FStar_Syntax_Syntax.as_arg k_app  in
                                  [uu____2497]  in
                                FStar_Syntax_Util.mk_app guard_free1
                                  uu____2488
                                 in
                              let pattern_guarded_body =
                                let uu____2501 =
                                  let uu____2502 =
                                    let uu____2509 =
                                      let uu____2510 =
                                        let uu____2521 =
                                          let uu____2524 =
                                            FStar_Syntax_Syntax.as_arg pat
                                             in
                                          [uu____2524]  in
                                        [uu____2521]  in
                                      FStar_Syntax_Syntax.Meta_pattern
                                        uu____2510
                                       in
                                    (body, uu____2509)  in
                                  FStar_Syntax_Syntax.Tm_meta uu____2502  in
                                mk1 uu____2501  in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu____2529 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula"
                           in
                        let body =
                          let uu____2533 =
                            let uu____2534 =
                              let uu____2535 =
                                let uu____2536 =
                                  FStar_Syntax_Syntax.bv_to_name wp  in
                                let uu____2539 =
                                  let uu____2548 = args_of_binders1 wp_args
                                     in
                                  let uu____2551 =
                                    let uu____2554 =
                                      let uu____2555 =
                                        FStar_Syntax_Syntax.bv_to_name k  in
                                      FStar_Syntax_Syntax.as_arg uu____2555
                                       in
                                    [uu____2554]  in
                                  FStar_List.append uu____2548 uu____2551  in
                                FStar_Syntax_Util.mk_app uu____2536
                                  uu____2539
                                 in
                              FStar_Syntax_Util.mk_imp equiv1 uu____2535  in
                            FStar_Syntax_Util.mk_forall_no_univ k uu____2534
                             in
                          FStar_Syntax_Util.abs gamma uu____2533
                            ret_gtot_type
                           in
                        let uu____2556 =
                          let uu____2557 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                          FStar_List.append binders uu____2557  in
                        FStar_Syntax_Util.abs uu____2556 body ret_gtot_type
                     in
                  let wp_ite1 =
                    let uu____2569 = mk_lid "wp_ite"  in
                    register env1 uu____2569 wp_ite  in
                  let wp_ite2 = mk_generic_app wp_ite1  in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let uu____2575 = FStar_Util.prefix gamma  in
                    match uu____2575 with
                    | (wp_args,post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun
                           in
                        let body =
                          let uu____2618 =
                            let uu____2619 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                (FStar_Pervasives_Native.fst post)
                               in
                            let uu____2622 =
                              let uu____2631 =
                                let uu____2632 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_Syntax_Syntax.as_arg uu____2632  in
                              [uu____2631]  in
                            FStar_Syntax_Util.mk_app uu____2619 uu____2622
                             in
                          FStar_Syntax_Util.mk_forall_no_univ x uu____2618
                           in
                        let uu____2633 =
                          let uu____2634 =
                            let uu____2641 =
                              FStar_Syntax_Syntax.binders_of_list [a1]  in
                            FStar_List.append uu____2641 gamma  in
                          FStar_List.append binders uu____2634  in
                        FStar_Syntax_Util.abs uu____2633 body ret_gtot_type
                     in
                  let null_wp1 =
                    let uu____2657 = mk_lid "null_wp"  in
                    register env1 uu____2657 null_wp  in
                  let null_wp2 = mk_generic_app null_wp1  in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1
                       in
                    let body =
                      let uu____2666 =
                        let uu____2675 =
                          let uu____2678 = FStar_Syntax_Syntax.bv_to_name a1
                             in
                          let uu____2679 =
                            let uu____2682 =
                              let uu____2685 =
                                let uu____2694 =
                                  let uu____2695 =
                                    FStar_Syntax_Syntax.bv_to_name a1  in
                                  FStar_Syntax_Syntax.as_arg uu____2695  in
                                [uu____2694]  in
                              FStar_Syntax_Util.mk_app null_wp2 uu____2685
                               in
                            let uu____2696 =
                              let uu____2701 =
                                FStar_Syntax_Syntax.bv_to_name wp  in
                              [uu____2701]  in
                            uu____2682 :: uu____2696  in
                          uu____2678 :: uu____2679  in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu____2675
                         in
                      FStar_Syntax_Util.mk_app stronger2 uu____2666  in
                    let uu____2704 =
                      let uu____2705 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp]  in
                      FStar_List.append binders uu____2705  in
                    FStar_Syntax_Util.abs uu____2704 body ret_tot_type  in
                  let wp_trivial1 =
                    let uu____2717 = mk_lid "wp_trivial"  in
                    register env1 uu____2717 wp_trivial  in
                  let wp_trivial2 = mk_generic_app wp_trivial1  in
                  ((let uu____2722 =
                      FStar_TypeChecker_Env.debug env1
                        (FStar_Options.Other "ED")
                       in
                    if uu____2722
                    then d "End Dijkstra monads for free"
                    else ());
                   (let c = FStar_Syntax_Subst.close binders  in
                    let uu____2727 =
                      let uu____2730 = FStar_ST.op_Bang sigelts  in
                      FStar_List.rev uu____2730  in
                    let uu____2799 =
                      let uu___299_2800 = ed  in
                      let uu____2801 =
                        let uu____2802 = c wp_if_then_else2  in
                        ([], uu____2802)  in
                      let uu____2805 =
                        let uu____2806 = c wp_ite2  in ([], uu____2806)  in
                      let uu____2809 =
                        let uu____2810 = c stronger2  in ([], uu____2810)  in
                      let uu____2813 =
                        let uu____2814 = c wp_close2  in ([], uu____2814)  in
                      let uu____2817 =
                        let uu____2818 = c wp_assert2  in ([], uu____2818)
                         in
                      let uu____2821 =
                        let uu____2822 = c wp_assume2  in ([], uu____2822)
                         in
                      let uu____2825 =
                        let uu____2826 = c null_wp2  in ([], uu____2826)  in
                      let uu____2829 =
                        let uu____2830 = c wp_trivial2  in ([], uu____2830)
                         in
                      {
                        FStar_Syntax_Syntax.cattributes =
                          (uu___299_2800.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___299_2800.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___299_2800.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders =
                          (uu___299_2800.FStar_Syntax_Syntax.binders);
                        FStar_Syntax_Syntax.signature =
                          (uu___299_2800.FStar_Syntax_Syntax.signature);
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___299_2800.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___299_2800.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else = uu____2801;
                        FStar_Syntax_Syntax.ite_wp = uu____2805;
                        FStar_Syntax_Syntax.stronger = uu____2809;
                        FStar_Syntax_Syntax.close_wp = uu____2813;
                        FStar_Syntax_Syntax.assert_p = uu____2817;
                        FStar_Syntax_Syntax.assume_p = uu____2821;
                        FStar_Syntax_Syntax.null_wp = uu____2825;
                        FStar_Syntax_Syntax.trivial = uu____2829;
                        FStar_Syntax_Syntax.repr =
                          (uu___299_2800.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___299_2800.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___299_2800.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___299_2800.FStar_Syntax_Syntax.actions)
                      }  in
                    (uu____2727, uu____2799)))))
  
type env_ = env[@@deriving show]
let get_env : env -> FStar_TypeChecker_Env.env = fun env  -> env.env 
let set_env : env -> FStar_TypeChecker_Env.env -> env =
  fun dmff_env  ->
    fun env'  ->
      let uu___300_2844 = dmff_env  in
      {
        env = env';
        subst = (uu___300_2844.subst);
        tc_const = (uu___300_2844.tc_const)
      }
  
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ [@@deriving show]
let uu___is_N : nm -> Prims.bool =
  fun projectee  -> match projectee with | N _0 -> true | uu____2857 -> false 
let __proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | N _0 -> _0 
let uu___is_M : nm -> Prims.bool =
  fun projectee  -> match projectee with | M _0 -> true | uu____2869 -> false 
let __proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ =
  fun projectee  -> match projectee with | M _0 -> _0 
type nm_ = nm[@@deriving show]
let nm_of_comp : FStar_Syntax_Syntax.comp' -> nm =
  fun uu___286_2879  ->
    match uu___286_2879 with
    | FStar_Syntax_Syntax.Total (t,uu____2881) -> N t
    | FStar_Syntax_Syntax.Comp c when
        FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___285_2894  ->
                match uu___285_2894 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____2895 -> false))
        -> M (c.FStar_Syntax_Syntax.result_typ)
    | FStar_Syntax_Syntax.Comp c ->
        let uu____2897 =
          let uu____2898 =
            let uu____2899 = FStar_Syntax_Syntax.mk_Comp c  in
            FStar_All.pipe_left FStar_Syntax_Print.comp_to_string uu____2899
             in
          FStar_Util.format1 "[nm_of_comp]: impossible (%s)" uu____2898  in
        failwith uu____2897
    | FStar_Syntax_Syntax.GTotal uu____2900 ->
        failwith "[nm_of_comp]: impossible (GTot)"
  
let string_of_nm : nm -> Prims.string =
  fun uu___287_2911  ->
    match uu___287_2911 with
    | N t ->
        let uu____2913 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "N[%s]" uu____2913
    | M t ->
        let uu____2915 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "M[%s]" uu____2915
  
let is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm =
  fun n1  ->
    match n1 with
    | FStar_Syntax_Syntax.Tm_arrow
        (uu____2919,{ FStar_Syntax_Syntax.n = n2;
                      FStar_Syntax_Syntax.pos = uu____2921;
                      FStar_Syntax_Syntax.vars = uu____2922;_})
        -> nm_of_comp n2
    | uu____2939 -> failwith "unexpected_argument: [is_monadic_arrow]"
  
let is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool =
  fun c  ->
    let uu____2947 = nm_of_comp c.FStar_Syntax_Syntax.n  in
    match uu____2947 with | M uu____2948 -> true | N uu____2949 -> false
  
exception Not_found 
let uu___is_Not_found : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Not_found  -> true | uu____2953 -> false
  
let double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun typ  ->
    let star_once typ1 =
      let uu____2963 =
        let uu____2970 =
          let uu____2971 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1  in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____2971  in
        [uu____2970]  in
      let uu____2972 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
         in
      FStar_Syntax_Util.arrow uu____2963 uu____2972  in
    let uu____2975 = FStar_All.pipe_right typ star_once  in
    FStar_All.pipe_left star_once uu____2975
  
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
        mk1
          (let uu____3012 =
             let uu____3025 =
               let uu____3032 =
                 let uu____3037 =
                   let uu____3038 = star_type' env a  in
                   FStar_Syntax_Syntax.null_bv uu____3038  in
                 let uu____3039 = FStar_Syntax_Syntax.as_implicit false  in
                 (uu____3037, uu____3039)  in
               [uu____3032]  in
             let uu____3048 =
               FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
             (uu____3025, uu____3048)  in
           FStar_Syntax_Syntax.Tm_arrow uu____3012)

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
      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____3076) ->
          let binders1 =
            FStar_List.map
              (fun uu____3112  ->
                 match uu____3112 with
                 | (bv,aqual) ->
                     let uu____3123 =
                       let uu___301_3124 = bv  in
                       let uu____3125 =
                         star_type' env bv.FStar_Syntax_Syntax.sort  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___301_3124.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___301_3124.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____3125
                       }  in
                     (uu____3123, aqual)) binders
             in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu____3128,{
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (hn,uu____3130);
                             FStar_Syntax_Syntax.pos = uu____3131;
                             FStar_Syntax_Syntax.vars = uu____3132;_})
               ->
               let uu____3157 =
                 let uu____3158 =
                   let uu____3171 =
                     let uu____3172 = star_type' env hn  in
                     FStar_Syntax_Syntax.mk_GTotal uu____3172  in
                   (binders1, uu____3171)  in
                 FStar_Syntax_Syntax.Tm_arrow uu____3158  in
               mk1 uu____3157
           | uu____3179 ->
               let uu____3180 = is_monadic_arrow t1.FStar_Syntax_Syntax.n  in
               (match uu____3180 with
                | N hn ->
                    let uu____3182 =
                      let uu____3183 =
                        let uu____3196 =
                          let uu____3197 = star_type' env hn  in
                          FStar_Syntax_Syntax.mk_Total uu____3197  in
                        (binders1, uu____3196)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3183  in
                    mk1 uu____3182
                | M a ->
                    let uu____3205 =
                      let uu____3206 =
                        let uu____3219 =
                          let uu____3226 =
                            let uu____3233 =
                              let uu____3238 =
                                let uu____3239 = mk_star_to_type1 env a  in
                                FStar_Syntax_Syntax.null_bv uu____3239  in
                              let uu____3240 =
                                FStar_Syntax_Syntax.as_implicit false  in
                              (uu____3238, uu____3240)  in
                            [uu____3233]  in
                          FStar_List.append binders1 uu____3226  in
                        let uu____3253 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        (uu____3219, uu____3253)  in
                      FStar_Syntax_Syntax.Tm_arrow uu____3206  in
                    mk1 uu____3205))
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let debug1 t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1  in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder ()  in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu____3319 = f x  in
                    FStar_Util.string_builder_append strb uu____3319);
                   FStar_List.iter
                     (fun x1  ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu____3326 = f x1  in
                         FStar_Util.string_builder_append strb uu____3326))
                     xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb)
               in
            let uu____3328 = FStar_Syntax_Print.term_to_string t2  in
            let uu____3329 = string_of_set FStar_Syntax_Print.bv_to_string s
               in
            FStar_Util.print2_warning "Dependency found in term %s : %s"
              uu____3328 uu____3329
             in
          let rec is_non_dependent_arrow ty n1 =
            let uu____3337 =
              let uu____3338 = FStar_Syntax_Subst.compress ty  in
              uu____3338.FStar_Syntax_Syntax.n  in
            match uu____3337 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____3359 =
                  let uu____3360 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                     in
                  Prims.op_Negation uu____3360  in
                if uu____3359
                then false
                else
                  (try
                     let non_dependent_or_raise s ty1 =
                       let sinter =
                         let uu____3386 = FStar_Syntax_Free.names ty1  in
                         FStar_Util.set_intersect uu____3386 s  in
                       let uu____3389 =
                         let uu____3390 = FStar_Util.set_is_empty sinter  in
                         Prims.op_Negation uu____3390  in
                       if uu____3389
                       then (debug1 ty1 sinter; FStar_Exn.raise Not_found)
                       else ()  in
                     let uu____3393 = FStar_Syntax_Subst.open_comp binders c
                        in
                     match uu____3393 with
                     | (binders1,c1) ->
                         let s =
                           FStar_List.fold_left
                             (fun s  ->
                                fun uu____3415  ->
                                  match uu____3415 with
                                  | (bv,uu____3425) ->
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
            | uu____3439 ->
                ((let uu____3441 = FStar_Syntax_Print.term_to_string ty  in
                  FStar_Util.print1_warning "Not a dependent arrow : %s"
                    uu____3441);
                 false)
             in
          let rec is_valid_application head2 =
            let uu____3446 =
              let uu____3447 = FStar_Syntax_Subst.compress head2  in
              uu____3447.FStar_Syntax_Syntax.n  in
            match uu____3446 with
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
                  (let uu____3452 = FStar_Syntax_Subst.compress head2  in
                   FStar_Syntax_Util.is_tuple_constructor uu____3452)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu____3454 =
                  FStar_TypeChecker_Env.lookup_lid env.env
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____3454 with
                 | ((uu____3463,ty),uu____3465) ->
                     let uu____3470 =
                       is_non_dependent_arrow ty (FStar_List.length args)  in
                     if uu____3470
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Inlining;
                           FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant] env.env t1
                          in
                       (match res.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_app uu____3478 -> true
                        | uu____3493 ->
                            ((let uu____3495 =
                                FStar_Syntax_Print.term_to_string head2  in
                              FStar_Util.print1_warning
                                "Got a term which might be a non-dependent user-defined data-type %s\n"
                                uu____3495);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu____3497 -> true
            | FStar_Syntax_Syntax.Tm_name uu____3498 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3500) ->
                is_valid_application t2
            | uu____3505 -> false  in
          let uu____3506 = is_valid_application head1  in
          if uu____3506
          then
            let uu____3507 =
              let uu____3508 =
                let uu____3523 =
                  FStar_List.map
                    (fun uu____3544  ->
                       match uu____3544 with
                       | (t2,qual) ->
                           let uu____3561 = star_type' env t2  in
                           (uu____3561, qual)) args
                   in
                (head1, uu____3523)  in
              FStar_Syntax_Syntax.Tm_app uu____3508  in
            mk1 uu____3507
          else
            (let uu____3571 =
               let uu____3572 =
                 let uu____3573 = FStar_Syntax_Print.term_to_string t1  in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu____3573
                  in
               FStar_Errors.Err uu____3572  in
             FStar_Exn.raise uu____3571)
      | FStar_Syntax_Syntax.Tm_bvar uu____3574 -> t1
      | FStar_Syntax_Syntax.Tm_name uu____3575 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____3576 -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu____3577 -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders,repr,something) ->
          let uu____3601 = FStar_Syntax_Subst.open_term binders repr  in
          (match uu____3601 with
           | (binders1,repr1) ->
               let env1 =
                 let uu___304_3609 = env  in
                 let uu____3610 =
                   FStar_TypeChecker_Env.push_binders env.env binders1  in
                 {
                   env = uu____3610;
                   subst = (uu___304_3609.subst);
                   tc_const = (uu___304_3609.tc_const)
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
               ((let uu___305_3630 = x1  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___305_3630.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___305_3630.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2,m) ->
          let uu____3637 =
            let uu____3638 =
              let uu____3645 = star_type' env t2  in (uu____3645, m)  in
            FStar_Syntax_Syntax.Tm_meta uu____3638  in
          mk1 uu____3637
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inl t2,FStar_Pervasives_Native.None ),something) ->
          let uu____3693 =
            let uu____3694 =
              let uu____3721 = star_type' env e  in
              let uu____3722 =
                let uu____3737 =
                  let uu____3744 = star_type' env t2  in
                  FStar_Util.Inl uu____3744  in
                (uu____3737, FStar_Pervasives_Native.None)  in
              (uu____3721, uu____3722, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3694  in
          mk1 uu____3693
      | FStar_Syntax_Syntax.Tm_ascribed
          (e,(FStar_Util.Inr c,FStar_Pervasives_Native.None ),something) ->
          let uu____3822 =
            let uu____3823 =
              let uu____3850 = star_type' env e  in
              let uu____3851 =
                let uu____3866 =
                  let uu____3873 =
                    star_type' env (FStar_Syntax_Util.comp_result c)  in
                  FStar_Util.Inl uu____3873  in
                (uu____3866, FStar_Pervasives_Native.None)  in
              (uu____3850, uu____3851, something)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____3823  in
          mk1 uu____3822
      | FStar_Syntax_Syntax.Tm_refine uu____3904 ->
          let uu____3911 =
            let uu____3912 =
              let uu____3913 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s"
                uu____3913
               in
            FStar_Errors.Err uu____3912  in
          FStar_Exn.raise uu____3911
      | FStar_Syntax_Syntax.Tm_uinst uu____3914 ->
          let uu____3921 =
            let uu____3922 =
              let uu____3923 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s"
                uu____3923
               in
            FStar_Errors.Err uu____3922  in
          FStar_Exn.raise uu____3921
      | FStar_Syntax_Syntax.Tm_constant uu____3924 ->
          let uu____3925 =
            let uu____3926 =
              let uu____3927 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu____3927
               in
            FStar_Errors.Err uu____3926  in
          FStar_Exn.raise uu____3925
      | FStar_Syntax_Syntax.Tm_match uu____3928 ->
          let uu____3951 =
            let uu____3952 =
              let uu____3953 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s"
                uu____3953
               in
            FStar_Errors.Err uu____3952  in
          FStar_Exn.raise uu____3951
      | FStar_Syntax_Syntax.Tm_let uu____3954 ->
          let uu____3967 =
            let uu____3968 =
              let uu____3969 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu____3969
               in
            FStar_Errors.Err uu____3968  in
          FStar_Exn.raise uu____3967
      | FStar_Syntax_Syntax.Tm_uvar uu____3970 ->
          let uu____3987 =
            let uu____3988 =
              let uu____3989 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s"
                uu____3989
               in
            FStar_Errors.Err uu____3988  in
          FStar_Exn.raise uu____3987
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____3990 =
            let uu____3991 =
              let uu____3992 = FStar_Syntax_Print.term_to_string t1  in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s"
                uu____3992
               in
            FStar_Errors.Err uu____3991  in
          FStar_Exn.raise uu____3990
      | FStar_Syntax_Syntax.Tm_delayed uu____3993 -> failwith "impossible"

let is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool
  =
  fun uu___289_4022  ->
    match uu___289_4022 with
    | FStar_Pervasives_Native.None  -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___288_4029  ->
                match uu___288_4029 with
                | FStar_Syntax_Syntax.CPS  -> true
                | uu____4030 -> false))
  
let rec is_C : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    let uu____4034 =
      let uu____4035 = FStar_Syntax_Subst.compress t  in
      uu____4035.FStar_Syntax_Syntax.n  in
    match uu____4034 with
    | FStar_Syntax_Syntax.Tm_app (head1,args) when
        FStar_Syntax_Util.is_tuple_constructor head1 ->
        let r =
          let uu____4061 =
            let uu____4062 = FStar_List.hd args  in
            FStar_Pervasives_Native.fst uu____4062  in
          is_C uu____4061  in
        if r
        then
          ((let uu____4078 =
              let uu____4079 =
                FStar_List.for_all
                  (fun uu____4087  ->
                     match uu____4087 with | (h,uu____4093) -> is_C h) args
                 in
              Prims.op_Negation uu____4079  in
            if uu____4078 then failwith "not a C (A * C)" else ());
           true)
        else
          ((let uu____4097 =
              let uu____4098 =
                FStar_List.for_all
                  (fun uu____4107  ->
                     match uu____4107 with
                     | (h,uu____4113) ->
                         let uu____4114 = is_C h  in
                         Prims.op_Negation uu____4114) args
                 in
              Prims.op_Negation uu____4098  in
            if uu____4097 then failwith "not a C (C * A)" else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____4134 = nm_of_comp comp.FStar_Syntax_Syntax.n  in
        (match uu____4134 with
         | M t1 ->
             ((let uu____4137 = is_C t1  in
               if uu____4137 then failwith "not a C (C -> C)" else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____4141) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4147) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____4153,uu____4154) -> is_C t1
    | uu____4195 -> false
  
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
          let uu____4218 =
            let uu____4219 =
              let uu____4234 = FStar_Syntax_Syntax.bv_to_name p  in
              let uu____4235 =
                let uu____4242 =
                  let uu____4247 = FStar_Syntax_Syntax.as_implicit false  in
                  (e, uu____4247)  in
                [uu____4242]  in
              (uu____4234, uu____4235)  in
            FStar_Syntax_Syntax.Tm_app uu____4219  in
          mk1 uu____4218  in
        let uu____4262 =
          let uu____4263 = FStar_Syntax_Syntax.mk_binder p  in [uu____4263]
           in
        FStar_Syntax_Util.abs uu____4262 body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
  
let is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool =
  fun uu___290_4266  ->
    match uu___290_4266 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4267 -> false
  
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
        let return_if uu____4442 =
          match uu____4442 with
          | (rec_nm,s_e,u_e) ->
              let check1 t1 t2 =
                let uu____4469 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu____4471 =
                       let uu____4472 =
                         FStar_TypeChecker_Rel.teq env.env t1 t2  in
                       FStar_TypeChecker_Rel.is_trivial uu____4472  in
                     Prims.op_Negation uu____4471)
                   in
                if uu____4469
                then
                  let uu____4473 =
                    let uu____4474 =
                      let uu____4475 = FStar_Syntax_Print.term_to_string e
                         in
                      let uu____4476 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____4477 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu____4475 uu____4476 uu____4477
                       in
                    FStar_Errors.Err uu____4474  in
                  FStar_Exn.raise uu____4473
                else ()  in
              (match (rec_nm, context_nm) with
               | (N t1,N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1,M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1,M t2) ->
                   (check1 t1 t2;
                    (let uu____4494 = mk_return env t1 s_e  in
                     ((M t1), uu____4494, u_e)))
               | (M t1,N t2) ->
                   let uu____4497 =
                     let uu____4498 =
                       let uu____4499 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____4500 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____4501 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu____4499 uu____4500 uu____4501
                        in
                     FStar_Errors.Err uu____4498  in
                   FStar_Exn.raise uu____4497)
           in
        let ensure_m env1 e2 =
          let strip_m uu___291_4542 =
            match uu___291_4542 with
            | (M t,s_e,u_e) -> (t, s_e, u_e)
            | uu____4558 -> failwith "impossible"  in
          match context_nm with
          | N t ->
              let uu____4578 =
                let uu____4579 =
                  let uu____4584 =
                    let uu____4585 = FStar_Syntax_Print.term_to_string t  in
                    Prims.strcat
                      "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                      uu____4585
                     in
                  (uu____4584, (e2.FStar_Syntax_Syntax.pos))  in
                FStar_Errors.Error uu____4579  in
              FStar_Exn.raise uu____4578
          | M uu____4592 ->
              let uu____4593 = check env1 e2 context_nm  in
              strip_m uu____4593
           in
        let uu____4600 =
          let uu____4601 = FStar_Syntax_Subst.compress e  in
          uu____4601.FStar_Syntax_Syntax.n  in
        match uu____4600 with
        | FStar_Syntax_Syntax.Tm_bvar uu____4610 ->
            let uu____4611 = infer env e  in return_if uu____4611
        | FStar_Syntax_Syntax.Tm_name uu____4618 ->
            let uu____4619 = infer env e  in return_if uu____4619
        | FStar_Syntax_Syntax.Tm_fvar uu____4626 ->
            let uu____4627 = infer env e  in return_if uu____4627
        | FStar_Syntax_Syntax.Tm_abs uu____4634 ->
            let uu____4651 = infer env e  in return_if uu____4651
        | FStar_Syntax_Syntax.Tm_constant uu____4658 ->
            let uu____4659 = infer env e  in return_if uu____4659
        | FStar_Syntax_Syntax.Tm_app uu____4666 ->
            let uu____4681 = infer env e  in return_if uu____4681
        | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
            mk_let env binding e2
              (fun env1  -> fun e21  -> check env1 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
            mk_match env e0 branches
              (fun env1  -> fun body  -> check env1 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1,uu____4749) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1,uu____4755) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____4761,uu____4762) ->
            check env e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu____4803 ->
            let uu____4816 =
              let uu____4817 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_let %s" uu____4817  in
            failwith uu____4816
        | FStar_Syntax_Syntax.Tm_type uu____4824 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu____4831 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu____4850 ->
            let uu____4857 =
              let uu____4858 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_refine %s" uu____4858  in
            failwith uu____4857
        | FStar_Syntax_Syntax.Tm_uvar uu____4865 ->
            let uu____4882 =
              let uu____4883 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu____4883  in
            failwith uu____4882
        | FStar_Syntax_Syntax.Tm_delayed uu____4890 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____4921 =
              let uu____4922 = FStar_Syntax_Print.term_to_string e  in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu____4922  in
            failwith uu____4921

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
      let uu____4946 =
        let uu____4947 = FStar_Syntax_Subst.compress e  in
        uu____4947.FStar_Syntax_Syntax.n  in
      match uu____4946 with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_abs (binders,body,rc_opt) ->
          let subst_rc_opt subst1 rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu____5006;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None ;
                  FStar_Syntax_Syntax.residual_flags = uu____5007;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None  -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu____5013 =
                  let uu___306_5014 = rc  in
                  let uu____5015 =
                    let uu____5020 =
                      let uu____5021 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ
                         in
                      FStar_Syntax_Subst.subst subst1 uu____5021  in
                    FStar_Pervasives_Native.Some uu____5020  in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___306_5014.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu____5015;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___306_5014.FStar_Syntax_Syntax.residual_flags)
                  }  in
                FStar_Pervasives_Native.Some uu____5013
             in
          let binders1 = FStar_Syntax_Subst.open_binders binders  in
          let subst1 = FStar_Syntax_Subst.opening_of_binders binders1  in
          let body1 = FStar_Syntax_Subst.subst subst1 body  in
          let rc_opt1 = subst_rc_opt subst1 rc_opt  in
          let env1 =
            let uu___307_5031 = env  in
            let uu____5032 =
              FStar_TypeChecker_Env.push_binders env.env binders1  in
            {
              env = uu____5032;
              subst = (uu___307_5031.subst);
              tc_const = (uu___307_5031.tc_const)
            }  in
          let s_binders =
            FStar_List.map
              (fun uu____5052  ->
                 match uu____5052 with
                 | (bv,qual) ->
                     let sort = star_type' env1 bv.FStar_Syntax_Syntax.sort
                        in
                     ((let uu___308_5065 = bv  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___308_5065.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___308_5065.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = sort
                       }), qual)) binders1
             in
          let uu____5066 =
            FStar_List.fold_left
              (fun uu____5095  ->
                 fun uu____5096  ->
                   match (uu____5095, uu____5096) with
                   | ((env2,acc),(bv,qual)) ->
                       let c = bv.FStar_Syntax_Syntax.sort  in
                       let uu____5144 = is_C c  in
                       if uu____5144
                       then
                         let xw =
                           let uu____5152 = star_type' env2 c  in
                           FStar_Syntax_Syntax.gen_bv
                             (Prims.strcat
                                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                "__w") FStar_Pervasives_Native.None
                             uu____5152
                            in
                         let x =
                           let uu___309_5154 = bv  in
                           let uu____5155 =
                             let uu____5158 =
                               FStar_Syntax_Syntax.bv_to_name xw  in
                             trans_F_ env2 c uu____5158  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___309_5154.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___309_5154.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu____5155
                           }  in
                         let env3 =
                           let uu___310_5160 = env2  in
                           let uu____5161 =
                             let uu____5164 =
                               let uu____5165 =
                                 let uu____5172 =
                                   FStar_Syntax_Syntax.bv_to_name xw  in
                                 (bv, uu____5172)  in
                               FStar_Syntax_Syntax.NT uu____5165  in
                             uu____5164 :: (env2.subst)  in
                           {
                             env = (uu___310_5160.env);
                             subst = uu____5161;
                             tc_const = (uu___310_5160.tc_const)
                           }  in
                         let uu____5173 =
                           let uu____5176 = FStar_Syntax_Syntax.mk_binder x
                              in
                           let uu____5177 =
                             let uu____5180 =
                               FStar_Syntax_Syntax.mk_binder xw  in
                             uu____5180 :: acc  in
                           uu____5176 :: uu____5177  in
                         (env3, uu____5173)
                       else
                         (let x =
                            let uu___311_5185 = bv  in
                            let uu____5186 =
                              star_type' env2 bv.FStar_Syntax_Syntax.sort  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___311_5185.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___311_5185.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu____5186
                            }  in
                          let uu____5189 =
                            let uu____5192 = FStar_Syntax_Syntax.mk_binder x
                               in
                            uu____5192 :: acc  in
                          (env2, uu____5189))) (env1, []) binders1
             in
          (match uu____5066 with
           | (env2,u_binders) ->
               let u_binders1 = FStar_List.rev u_binders  in
               let uu____5212 =
                 let check_what =
                   let uu____5230 = is_monadic rc_opt1  in
                   if uu____5230 then check_m else check_n  in
                 let uu____5242 = check_what env2 body1  in
                 match uu____5242 with
                 | (t,s_body,u_body) ->
                     let uu____5258 =
                       let uu____5259 =
                         let uu____5260 = is_monadic rc_opt1  in
                         if uu____5260 then M t else N t  in
                       comp_of_nm uu____5259  in
                     (uu____5258, s_body, u_body)
                  in
               (match uu____5212 with
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
                                 let uu____5285 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___292_5289  ->
                                           match uu___292_5289 with
                                           | FStar_Syntax_Syntax.CPS  -> true
                                           | uu____5290 -> false))
                                    in
                                 if uu____5285
                                 then
                                   let uu____5291 =
                                     FStar_List.filter
                                       (fun uu___293_5295  ->
                                          match uu___293_5295 with
                                          | FStar_Syntax_Syntax.CPS  -> false
                                          | uu____5296 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu____5291
                                 else rc  in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu____5305 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___294_5309  ->
                                         match uu___294_5309 with
                                         | FStar_Syntax_Syntax.CPS  -> true
                                         | uu____5310 -> false))
                                  in
                               if uu____5305
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___295_5317  ->
                                        match uu___295_5317 with
                                        | FStar_Syntax_Syntax.CPS  -> false
                                        | uu____5318 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags
                                    in
                                 let uu____5319 =
                                   let uu____5320 =
                                     let uu____5325 = double_star rt  in
                                     FStar_Pervasives_Native.Some uu____5325
                                      in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____5320 flags
                                    in
                                 FStar_Pervasives_Native.Some uu____5319
                               else
                                 (let uu____5327 =
                                    let uu___312_5328 = rc  in
                                    let uu____5329 =
                                      let uu____5334 = star_type' env2 rt  in
                                      FStar_Pervasives_Native.Some uu____5334
                                       in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___312_5328.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu____5329;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___312_5328.FStar_Syntax_Syntax.residual_flags)
                                    }  in
                                  FStar_Pervasives_Native.Some uu____5327))
                       in
                    let uu____5335 =
                      let comp1 =
                        let uu____5345 = is_monadic rc_opt1  in
                        let uu____5346 =
                          FStar_Syntax_Subst.subst env2.subst s_body  in
                        trans_G env2 (FStar_Syntax_Util.comp_result comp)
                          uu____5345 uu____5346
                         in
                      let uu____5347 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Util.Inr comp1),
                            FStar_Pervasives_Native.None)
                         in
                      (uu____5347,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1)))
                       in
                    (match uu____5335 with
                     | (u_body1,u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body  in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders  in
                         let s_term =
                           let uu____5389 =
                             let uu____5390 =
                               let uu____5407 =
                                 let uu____5410 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1
                                    in
                                 subst_rc_opt uu____5410 s_rc_opt  in
                               (s_binders1, s_body1, uu____5407)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5390  in
                           mk1 uu____5389  in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1  in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1  in
                         let u_term =
                           let uu____5420 =
                             let uu____5421 =
                               let uu____5438 =
                                 let uu____5441 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2
                                    in
                                 subst_rc_opt uu____5441 u_rc_opt  in
                               (u_binders2, u_body2, uu____5438)  in
                             FStar_Syntax_Syntax.Tm_abs uu____5421  in
                           mk1 uu____5420  in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu____5451;_};
            FStar_Syntax_Syntax.fv_delta = uu____5452;
            FStar_Syntax_Syntax.fv_qual = uu____5453;_}
          ->
          let uu____5456 =
            let uu____5461 = FStar_TypeChecker_Env.lookup_lid env.env lid  in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu____5461  in
          (match uu____5456 with
           | (uu____5492,t) ->
               let uu____5494 =
                 let uu____5495 = normalize1 t  in N uu____5495  in
               (uu____5494, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5496;
             FStar_Syntax_Syntax.vars = uu____5497;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5560 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5560 with
           | (unary_op,uu____5582) ->
               let head1 = mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a]))
                  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5641;
             FStar_Syntax_Syntax.vars = uu____5642;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____5718 = FStar_Syntax_Util.head_and_args e  in
          (match uu____5718 with
           | (unary_op,uu____5740) ->
               let head1 =
                 mk1 (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2]))  in
               let t = mk1 (FStar_Syntax_Syntax.Tm_app (head1, rest1))  in
               infer env t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____5805;
             FStar_Syntax_Syntax.vars = uu____5806;_},(a,FStar_Pervasives_Native.None
                                                       )::[])
          ->
          let uu____5844 = infer env a  in
          (match uu____5844 with
           | (t,s,u) ->
               let uu____5860 = FStar_Syntax_Util.head_and_args e  in
               (match uu____5860 with
                | (head1,uu____5882) ->
                    let uu____5903 =
                      let uu____5904 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid
                         in
                      N uu____5904  in
                    let uu____5905 =
                      let uu____5908 =
                        let uu____5909 =
                          let uu____5924 =
                            let uu____5927 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____5927]  in
                          (head1, uu____5924)  in
                        FStar_Syntax_Syntax.Tm_app uu____5909  in
                      mk1 uu____5908  in
                    let uu____5932 =
                      let uu____5935 =
                        let uu____5936 =
                          let uu____5951 =
                            let uu____5954 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____5954]  in
                          (head1, uu____5951)  in
                        FStar_Syntax_Syntax.Tm_app uu____5936  in
                      mk1 uu____5935  in
                    (uu____5903, uu____5905, uu____5932)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____5963;
             FStar_Syntax_Syntax.vars = uu____5964;_},(a1,uu____5966)::a2::[])
          ->
          let uu____6008 = infer env a1  in
          (match uu____6008 with
           | (t,s,u) ->
               let uu____6024 = FStar_Syntax_Util.head_and_args e  in
               (match uu____6024 with
                | (head1,uu____6046) ->
                    let uu____6067 =
                      let uu____6070 =
                        let uu____6071 =
                          let uu____6086 =
                            let uu____6089 = FStar_Syntax_Syntax.as_arg s  in
                            [uu____6089; a2]  in
                          (head1, uu____6086)  in
                        FStar_Syntax_Syntax.Tm_app uu____6071  in
                      mk1 uu____6070  in
                    let uu____6106 =
                      let uu____6109 =
                        let uu____6110 =
                          let uu____6125 =
                            let uu____6128 = FStar_Syntax_Syntax.as_arg u  in
                            [uu____6128; a2]  in
                          (head1, uu____6125)  in
                        FStar_Syntax_Syntax.Tm_app uu____6110  in
                      mk1 uu____6109  in
                    (t, uu____6067, uu____6106)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____6149;
             FStar_Syntax_Syntax.vars = uu____6150;_},uu____6151)
          ->
          let uu____6172 =
            let uu____6173 =
              let uu____6178 =
                let uu____6179 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6179
                 in
              (uu____6178, (e.FStar_Syntax_Syntax.pos))  in
            FStar_Errors.Error uu____6173  in
          FStar_Exn.raise uu____6172
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____6186;
             FStar_Syntax_Syntax.vars = uu____6187;_},uu____6188)
          ->
          let uu____6209 =
            let uu____6210 =
              let uu____6215 =
                let uu____6216 = FStar_Syntax_Print.term_to_string e  in
                FStar_Util.format1 "DMFF: Ill-applied constant %s" uu____6216
                 in
              (uu____6215, (e.FStar_Syntax_Syntax.pos))  in
            FStar_Errors.Error uu____6210  in
          FStar_Exn.raise uu____6209
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let uu____6245 = check_n env head1  in
          (match uu____6245 with
           | (t_head,s_head,u_head) ->
               let is_arrow t =
                 let uu____6265 =
                   let uu____6266 = FStar_Syntax_Subst.compress t  in
                   uu____6266.FStar_Syntax_Syntax.n  in
                 match uu____6265 with
                 | FStar_Syntax_Syntax.Tm_arrow uu____6269 -> true
                 | uu____6282 -> false  in
               let rec flatten1 t =
                 let uu____6299 =
                   let uu____6300 = FStar_Syntax_Subst.compress t  in
                   uu____6300.FStar_Syntax_Syntax.n  in
                 match uu____6299 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,{
                                FStar_Syntax_Syntax.n =
                                  FStar_Syntax_Syntax.Total (t1,uu____6317);
                                FStar_Syntax_Syntax.pos = uu____6318;
                                FStar_Syntax_Syntax.vars = uu____6319;_})
                     when is_arrow t1 ->
                     let uu____6344 = flatten1 t1  in
                     (match uu____6344 with
                      | (binders',comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____6426,uu____6427)
                     -> flatten1 e1
                 | uu____6468 ->
                     let uu____6469 =
                       let uu____6470 =
                         let uu____6471 =
                           FStar_Syntax_Print.term_to_string t_head  in
                         FStar_Util.format1 "%s: not a function type"
                           uu____6471
                          in
                       FStar_Errors.Err uu____6470  in
                     FStar_Exn.raise uu____6469
                  in
               let uu____6484 = flatten1 t_head  in
               (match uu____6484 with
                | (binders,comp) ->
                    let n1 = FStar_List.length binders  in
                    let n' = FStar_List.length args  in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu____6544 =
                          let uu____6545 =
                            let uu____6546 = FStar_Util.string_of_int n1  in
                            let uu____6553 =
                              FStar_Util.string_of_int (n' - n1)  in
                            let uu____6564 = FStar_Util.string_of_int n1  in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu____6546 uu____6553 uu____6564
                             in
                          FStar_Errors.Err uu____6545  in
                        FStar_Exn.raise uu____6544)
                     else ();
                     (let uu____6572 =
                        FStar_Syntax_Subst.open_comp binders comp  in
                      match uu____6572 with
                      | (binders1,comp1) ->
                          let rec final_type subst1 uu____6613 args1 =
                            match uu____6613 with
                            | (binders2,comp2) ->
                                (match (binders2, args1) with
                                 | ([],[]) ->
                                     let uu____6687 =
                                       let uu____6688 =
                                         FStar_Syntax_Subst.subst_comp subst1
                                           comp2
                                          in
                                       uu____6688.FStar_Syntax_Syntax.n  in
                                     nm_of_comp uu____6687
                                 | (binders3,[]) ->
                                     let uu____6718 =
                                       let uu____6719 =
                                         let uu____6722 =
                                           let uu____6723 =
                                             mk1
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2))
                                              in
                                           FStar_Syntax_Subst.subst subst1
                                             uu____6723
                                            in
                                         FStar_Syntax_Subst.compress
                                           uu____6722
                                          in
                                       uu____6719.FStar_Syntax_Syntax.n  in
                                     (match uu____6718 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4,comp3) ->
                                          let uu____6748 =
                                            let uu____6749 =
                                              let uu____6750 =
                                                let uu____6763 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3
                                                   in
                                                (binders4, uu____6763)  in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu____6750
                                               in
                                            mk1 uu____6749  in
                                          N uu____6748
                                      | uu____6770 -> failwith "wat?")
                                 | ([],uu____6771::uu____6772) ->
                                     failwith "just checked that?!"
                                 | ((bv,uu____6812)::binders3,(arg,uu____6815)::args2)
                                     ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst1) (binders3, comp2) args2)
                             in
                          let final_type1 =
                            final_type [] (binders1, comp1) args  in
                          let uu____6868 = FStar_List.splitAt n' binders1  in
                          (match uu____6868 with
                           | (binders2,uu____6900) ->
                               let uu____6925 =
                                 let uu____6944 =
                                   FStar_List.map2
                                     (fun uu____6992  ->
                                        fun uu____6993  ->
                                          match (uu____6992, uu____6993) with
                                          | ((bv,uu____7025),(arg,q)) ->
                                              let uu____7036 =
                                                let uu____7037 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort
                                                   in
                                                uu____7037.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____7036 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu____7054 ->
                                                   let arg1 = (arg, q)  in
                                                   (arg1, [arg1])
                                               | uu____7078 ->
                                                   let uu____7079 =
                                                     check_n env arg  in
                                                   (match uu____7079 with
                                                    | (uu____7100,s_arg,u_arg)
                                                        ->
                                                        let uu____7103 =
                                                          let uu____7110 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort
                                                             in
                                                          if uu____7110
                                                          then
                                                            let uu____7117 =
                                                              let uu____7122
                                                                =
                                                                FStar_Syntax_Subst.subst
                                                                  env.subst
                                                                  s_arg
                                                                 in
                                                              (uu____7122, q)
                                                               in
                                                            [uu____7117;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)]
                                                           in
                                                        ((s_arg, q),
                                                          uu____7103))))
                                     binders2 args
                                    in
                                 FStar_List.split uu____6944  in
                               (match uu____6925 with
                                | (s_args,u_args) ->
                                    let u_args1 = FStar_List.flatten u_args
                                       in
                                    let uu____7211 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args))
                                       in
                                    let uu____7220 =
                                      mk1
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1))
                                       in
                                    (final_type1, uu____7211, uu____7220)))))))
      | FStar_Syntax_Syntax.Tm_let ((false ,binding::[]),e2) ->
          mk_let env binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0,branches) ->
          mk_match env e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1,uu____7286) -> infer env e1
      | FStar_Syntax_Syntax.Tm_meta (e1,uu____7292) -> infer env e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1,uu____7298,uu____7299) ->
          infer env e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu____7341 = let uu____7342 = env.tc_const c  in N uu____7342
             in
          (uu____7341, e, e)
      | FStar_Syntax_Syntax.Tm_let uu____7343 ->
          let uu____7356 =
            let uu____7357 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_let %s" uu____7357  in
          failwith uu____7356
      | FStar_Syntax_Syntax.Tm_type uu____7364 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu____7371 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu____7390 ->
          let uu____7397 =
            let uu____7398 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu____7398  in
          failwith uu____7397
      | FStar_Syntax_Syntax.Tm_uvar uu____7405 ->
          let uu____7422 =
            let uu____7423 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu____7423  in
          failwith uu____7422
      | FStar_Syntax_Syntax.Tm_delayed uu____7430 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let uu____7461 =
            let uu____7462 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu____7462  in
          failwith uu____7461

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
          let uu____7507 = check_n env e0  in
          match uu____7507 with
          | (uu____7520,s_e0,u_e0) ->
              let uu____7523 =
                let uu____7552 =
                  FStar_List.map
                    (fun b  ->
                       let uu____7613 = FStar_Syntax_Subst.open_branch b  in
                       match uu____7613 with
                       | (pat,FStar_Pervasives_Native.None ,body) ->
                           let env1 =
                             let uu___313_7655 = env  in
                             let uu____7656 =
                               let uu____7657 =
                                 FStar_Syntax_Syntax.pat_bvs pat  in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env.env
                                 uu____7657
                                in
                             {
                               env = uu____7656;
                               subst = (uu___313_7655.subst);
                               tc_const = (uu___313_7655.tc_const)
                             }  in
                           let uu____7660 = f env1 body  in
                           (match uu____7660 with
                            | (nm,s_body,u_body) ->
                                (nm,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu____7732 ->
                           FStar_Exn.raise
                             (FStar_Errors.Err
                                "No when clauses in the definition language"))
                    branches
                   in
                FStar_List.split uu____7552  in
              (match uu____7523 with
               | (nms,branches1) ->
                   let t1 =
                     let uu____7834 = FStar_List.hd nms  in
                     match uu____7834 with | M t1 -> t1 | N t1 -> t1  in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___296_7840  ->
                          match uu___296_7840 with
                          | M uu____7841 -> true
                          | uu____7842 -> false) nms
                      in
                   let uu____7843 =
                     let uu____7880 =
                       FStar_List.map2
                         (fun nm  ->
                            fun uu____7970  ->
                              match uu____7970 with
                              | (pat,guard,(s_body,u_body,original_body)) ->
                                  (match (nm, has_m) with
                                   | (N t2,false ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2,true ) ->
                                       (nm, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2,true ) ->
                                       let uu____8147 =
                                         check env original_body (M t2)  in
                                       (match uu____8147 with
                                        | (uu____8184,s_body1,u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu____8223,false ) ->
                                       failwith "impossible")) nms branches1
                        in
                     FStar_List.unzip3 uu____7880  in
                   (match uu____7843 with
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
                              (fun uu____8407  ->
                                 match uu____8407 with
                                 | (pat,guard,s_body) ->
                                     let s_body1 =
                                       let uu____8458 =
                                         let uu____8459 =
                                           let uu____8474 =
                                             let uu____8481 =
                                               let uu____8486 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p
                                                  in
                                               let uu____8487 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false
                                                  in
                                               (uu____8486, uu____8487)  in
                                             [uu____8481]  in
                                           (s_body, uu____8474)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____8459
                                          in
                                       mk1 uu____8458  in
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
                            let uu____8519 =
                              let uu____8520 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____8520]  in
                            let uu____8521 =
                              mk1
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, s_branches2))
                               in
                            FStar_Syntax_Util.abs uu____8519 uu____8521
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let t1_star =
                            let uu____8527 =
                              let uu____8534 =
                                let uu____8535 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type
                                   in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu____8535
                                 in
                              [uu____8534]  in
                            let uu____8536 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0
                               in
                            FStar_Syntax_Util.arrow uu____8527 uu____8536  in
                          let uu____8539 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None))
                             in
                          let uu____8578 =
                            mk1
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, u_branches1))
                             in
                          ((M t1), uu____8539, uu____8578)
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
                           let uu____8595 =
                             let uu____8598 =
                               let uu____8599 =
                                 let uu____8626 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, s_branches1))
                                    in
                                 (uu____8626,
                                   ((FStar_Util.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)
                                  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____8599  in
                             mk1 uu____8598  in
                           let uu____8663 =
                             mk1
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, u_branches1))
                              in
                           ((N t1), uu____8595, uu____8663))))

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
              let uu____8710 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____8710]  in
            let uu____8711 = FStar_Syntax_Subst.open_term x_binders e2  in
            match uu____8711 with
            | (x_binders1,e21) ->
                let uu____8724 = infer env e1  in
                (match uu____8724 with
                 | (N t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu____8741 = is_C t1  in
                       if uu____8741
                       then
                         let uu___314_8742 = binding  in
                         let uu____8743 =
                           let uu____8746 =
                             FStar_Syntax_Subst.subst env.subst s_e1  in
                           trans_F_ env t1 uu____8746  in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___314_8742.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___314_8742.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu____8743;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___314_8742.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___314_8742.FStar_Syntax_Syntax.lbdef)
                         }
                       else binding  in
                     let env1 =
                       let uu___315_8749 = env  in
                       let uu____8750 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___316_8752 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___316_8752.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___316_8752.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____8750;
                         subst = (uu___315_8749.subst);
                         tc_const = (uu___315_8749.tc_const)
                       }  in
                     let uu____8753 = proceed env1 e21  in
                     (match uu____8753 with
                      | (nm_rec,s_e2,u_e2) ->
                          let s_binding =
                            let uu___317_8770 = binding  in
                            let uu____8771 =
                              star_type' env1
                                binding.FStar_Syntax_Syntax.lbtyp
                               in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___317_8770.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___317_8770.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu____8771;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___317_8770.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___317_8770.FStar_Syntax_Syntax.lbdef)
                            }  in
                          let uu____8774 =
                            let uu____8777 =
                              let uu____8778 =
                                let uu____8791 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2
                                   in
                                ((false,
                                   [(let uu___318_8801 = s_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___318_8801.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___318_8801.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___318_8801.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___318_8801.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1
                                     })]), uu____8791)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____8778  in
                            mk1 uu____8777  in
                          let uu____8802 =
                            let uu____8805 =
                              let uu____8806 =
                                let uu____8819 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___319_8829 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___319_8829.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___319_8829.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___319_8829.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___319_8829.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8819)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____8806  in
                            mk1 uu____8805  in
                          (nm_rec, uu____8774, uu____8802))
                 | (M t1,s_e1,u_e1) ->
                     let u_binding =
                       let uu___320_8838 = binding  in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___320_8838.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___320_8838.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___320_8838.FStar_Syntax_Syntax.lbdef)
                       }  in
                     let env1 =
                       let uu___321_8840 = env  in
                       let uu____8841 =
                         FStar_TypeChecker_Env.push_bv env.env
                           (let uu___322_8843 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___322_8843.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___322_8843.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            })
                          in
                       {
                         env = uu____8841;
                         subst = (uu___321_8840.subst);
                         tc_const = (uu___321_8840.tc_const)
                       }  in
                     let uu____8844 = ensure_m env1 e21  in
                     (match uu____8844 with
                      | (t2,s_e2,u_e2) ->
                          let p_type = mk_star_to_type mk1 env1 t2  in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type
                             in
                          let s_e21 =
                            let uu____8867 =
                              let uu____8868 =
                                let uu____8883 =
                                  let uu____8890 =
                                    let uu____8895 =
                                      FStar_Syntax_Syntax.bv_to_name p  in
                                    let uu____8896 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____8895, uu____8896)  in
                                  [uu____8890]  in
                                (s_e2, uu____8883)  in
                              FStar_Syntax_Syntax.Tm_app uu____8868  in
                            mk1 uu____8867  in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let body =
                            let uu____8915 =
                              let uu____8916 =
                                let uu____8931 =
                                  let uu____8938 =
                                    let uu____8943 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (s_e22, uu____8943)  in
                                  [uu____8938]  in
                                (s_e1, uu____8931)  in
                              FStar_Syntax_Syntax.Tm_app uu____8916  in
                            mk1 uu____8915  in
                          let uu____8958 =
                            let uu____8959 =
                              let uu____8960 =
                                FStar_Syntax_Syntax.mk_binder p  in
                              [uu____8960]  in
                            FStar_Syntax_Util.abs uu____8959 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0))
                             in
                          let uu____8961 =
                            let uu____8964 =
                              let uu____8965 =
                                let uu____8978 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2
                                   in
                                ((false,
                                   [(let uu___323_8988 = u_binding  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___323_8988.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___323_8988.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___323_8988.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___323_8988.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1
                                     })]), uu____8978)
                                 in
                              FStar_Syntax_Syntax.Tm_let uu____8965  in
                            mk1 uu____8964  in
                          ((M t2), uu____8958, uu____8961)))

and check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9000 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        N uu____9000  in
      let uu____9001 = check env e mn  in
      match uu____9001 with
      | (N t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9017 -> failwith "[check_n]: impossible"

and check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun e  ->
      let mn =
        let uu____9039 =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
           in
        M uu____9039  in
      let uu____9040 = check env e mn  in
      match uu____9040 with
      | (M t,s_e,u_e) -> (t, s_e, u_e)
      | uu____9056 -> failwith "[check_m]: impossible"

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
        (let uu____9086 =
           let uu____9087 = is_C c  in Prims.op_Negation uu____9087  in
         if uu____9086 then failwith "not a C" else ());
        (let mk1 x =
           FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
             c.FStar_Syntax_Syntax.pos
            in
         let uu____9095 =
           let uu____9096 = FStar_Syntax_Subst.compress c  in
           uu____9096.FStar_Syntax_Syntax.n  in
         match uu____9095 with
         | FStar_Syntax_Syntax.Tm_app (head1,args) ->
             let uu____9121 = FStar_Syntax_Util.head_and_args wp  in
             (match uu____9121 with
              | (wp_head,wp_args) ->
                  ((let uu____9159 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu____9173 =
                           let uu____9174 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange
                              in
                           FStar_Syntax_Util.is_constructor wp_head
                             uu____9174
                            in
                         Prims.op_Negation uu____9173)
                       in
                    if uu____9159 then failwith "mismatch" else ());
                   (let uu____9182 =
                      let uu____9183 =
                        let uu____9198 =
                          FStar_List.map2
                            (fun uu____9226  ->
                               fun uu____9227  ->
                                 match (uu____9226, uu____9227) with
                                 | ((arg,q),(wp_arg,q')) ->
                                     let print_implicit q1 =
                                       let uu____9264 =
                                         FStar_Syntax_Syntax.is_implicit q1
                                          in
                                       if uu____9264
                                       then "implicit"
                                       else "explicit"  in
                                     (if q <> q'
                                      then
                                        (let uu____9267 = print_implicit q
                                            in
                                         let uu____9268 = print_implicit q'
                                            in
                                         FStar_Util.print2_warning
                                           "Incoherent implicit qualifiers %b %b\n"
                                           uu____9267 uu____9268)
                                      else ();
                                      (let uu____9270 =
                                         trans_F_ env arg wp_arg  in
                                       (uu____9270, q)))) args wp_args
                           in
                        (head1, uu____9198)  in
                      FStar_Syntax_Syntax.Tm_app uu____9183  in
                    mk1 uu____9182)))
         | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders  in
             let uu____9304 = FStar_Syntax_Subst.open_comp binders1 comp  in
             (match uu____9304 with
              | (binders_orig,comp1) ->
                  let uu____9311 =
                    let uu____9326 =
                      FStar_List.map
                        (fun uu____9360  ->
                           match uu____9360 with
                           | (bv,q) ->
                               let h = bv.FStar_Syntax_Syntax.sort  in
                               let uu____9380 = is_C h  in
                               if uu____9380
                               then
                                 let w' =
                                   let uu____9392 = star_type' env h  in
                                   FStar_Syntax_Syntax.gen_bv
                                     (Prims.strcat
                                        (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                        "__w'") FStar_Pervasives_Native.None
                                     uu____9392
                                    in
                                 let uu____9393 =
                                   let uu____9400 =
                                     let uu____9407 =
                                       let uu____9412 =
                                         let uu____9413 =
                                           let uu____9414 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w'
                                              in
                                           trans_F_ env h uu____9414  in
                                         FStar_Syntax_Syntax.null_bv
                                           uu____9413
                                          in
                                       (uu____9412, q)  in
                                     [uu____9407]  in
                                   (w', q) :: uu____9400  in
                                 (w', uu____9393)
                               else
                                 (let x =
                                    let uu____9435 = star_type' env h  in
                                    FStar_Syntax_Syntax.gen_bv
                                      (Prims.strcat
                                         (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "__x") FStar_Pervasives_Native.None
                                      uu____9435
                                     in
                                  (x, [(x, q)]))) binders_orig
                       in
                    FStar_List.split uu____9326  in
                  (match uu____9311 with
                   | (bvs,binders2) ->
                       let binders3 = FStar_List.flatten binders2  in
                       let comp2 =
                         let uu____9490 =
                           let uu____9493 =
                             FStar_Syntax_Syntax.binders_of_list bvs  in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu____9493
                            in
                         FStar_Syntax_Subst.subst_comp uu____9490 comp1  in
                       let app =
                         let uu____9497 =
                           let uu____9498 =
                             let uu____9513 =
                               FStar_List.map
                                 (fun bv  ->
                                    let uu____9528 =
                                      FStar_Syntax_Syntax.bv_to_name bv  in
                                    let uu____9529 =
                                      FStar_Syntax_Syntax.as_implicit false
                                       in
                                    (uu____9528, uu____9529)) bvs
                                in
                             (wp, uu____9513)  in
                           FStar_Syntax_Syntax.Tm_app uu____9498  in
                         mk1 uu____9497  in
                       let comp3 =
                         let uu____9537 = type_of_comp comp2  in
                         let uu____9538 = is_monadic_comp comp2  in
                         trans_G env uu____9537 uu____9538 app  in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e,uu____9540,uu____9541) ->
             trans_F_ env e wp
         | uu____9582 -> failwith "impossible trans_F_")

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
            let uu____9587 =
              let uu____9588 = star_type' env h  in
              let uu____9591 =
                let uu____9600 =
                  let uu____9605 = FStar_Syntax_Syntax.as_implicit false  in
                  (wp, uu____9605)  in
                [uu____9600]  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu____9588;
                FStar_Syntax_Syntax.effect_args = uu____9591;
                FStar_Syntax_Syntax.flags = []
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____9587
          else
            (let uu____9615 = trans_F_ env h wp  in
             FStar_Syntax_Syntax.mk_Total uu____9615)

let n :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  FStar_TypeChecker_Normalize.normalize
    [FStar_TypeChecker_Normalize.Beta;
    FStar_TypeChecker_Normalize.UnfoldUntil
      FStar_Syntax_Syntax.Delta_constant;
    FStar_TypeChecker_Normalize.NoDeltaSteps;
    FStar_TypeChecker_Normalize.Eager_unfolding;
    FStar_TypeChecker_Normalize.EraseUniverses]
  
let star_type : env -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ =
  fun env  ->
    fun t  -> let uu____9626 = n env.env t  in star_type' env uu____9626
  
let star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  -> let uu____9641 = n env.env t  in check_n env uu____9641
  
let trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun c  ->
      fun wp  ->
        let uu____9651 = n env.env c  in
        let uu____9652 = n env.env wp  in trans_F_ env uu____9651 uu____9652
  