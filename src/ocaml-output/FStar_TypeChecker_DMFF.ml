open Prims
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  subst: FStar_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStar_Const.sconst -> FStar_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> tcenv
let (__proj__Mkenv__item__subst :
  env -> FStar_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> subst
let (__proj__Mkenv__item__tc_const :
  env -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> tc_const
let (empty :
  FStar_TypeChecker_Env.env ->
    (FStar_Const.sconst -> FStar_Syntax_Syntax.typ) -> env)
  = fun env1 -> fun tc_const -> { tcenv = env1; subst = []; tc_const }
let (gen_wps_for_free :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.bv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.eff_decl ->
            (FStar_Syntax_Syntax.sigelts * FStar_Syntax_Syntax.eff_decl))
  =
  fun env1 ->
    fun binders ->
      fun a ->
        fun wp_a ->
          fun ed ->
            let wp_a1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.EraseUniverses] env1 wp_a in
            let a1 =
              let uu___ = a in
              let uu___1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.EraseUniverses] env1
                  a.FStar_Syntax_Syntax.sort in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu___1
              } in
            let d s = FStar_Util.print1 "\027[01;36m%s\027[00m\n" s in
            (let uu___1 =
               FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED") in
             if uu___1
             then
               (d "Elaborating extra WP combinators";
                (let uu___3 = FStar_Syntax_Print.term_to_string wp_a1 in
                 FStar_Util.print1 "wp_a is: %s\n" uu___3))
             else ());
            (let rec collect_binders t =
               let t1 = FStar_Syntax_Util.unascribe t in
               let uu___1 =
                 let uu___2 = FStar_Syntax_Subst.compress t1 in
                 uu___2.FStar_Syntax_Syntax.n in
               match uu___1 with
               | FStar_Syntax_Syntax.Tm_arrow (bs, comp) ->
                   let rest =
                     match comp.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Total (t2, uu___2) -> t2
                     | uu___2 ->
                         let uu___3 =
                           let uu___4 =
                             let uu___5 =
                               FStar_Syntax_Print.comp_to_string comp in
                             FStar_Util.format1
                               "wp_a contains non-Tot arrow: %s" uu___5 in
                           (FStar_Errors.Error_UnexpectedDM4FType, uu___4) in
                         FStar_Errors.raise_error uu___3
                           comp.FStar_Syntax_Syntax.pos in
                   let uu___2 = collect_binders rest in
                   FStar_List.append bs uu___2
               | FStar_Syntax_Syntax.Tm_type uu___2 -> []
               | uu___2 ->
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                       FStar_Util.format1
                         "wp_a doesn't end in Type0, but rather in %s" uu___5 in
                     (FStar_Errors.Error_UnexpectedDM4FType, uu___4) in
                   FStar_Errors.raise_error uu___3 t1.FStar_Syntax_Syntax.pos in
             let mk_lid name = FStar_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu___1 = collect_binders wp_a1 in
               FStar_All.pipe_right uu___1 FStar_Syntax_Util.name_binders in
             (let uu___2 =
                FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED") in
              if uu___2
              then
                let uu___3 =
                  let uu___4 =
                    FStar_Syntax_Print.binders_to_string ", " gamma in
                  FStar_Util.format1 "Gamma is %s\n" uu___4 in
                d uu___3
              else ());
             (let unknown = FStar_Syntax_Syntax.tun in
              let mk x = FStar_Syntax_Syntax.mk x FStar_Range.dummyRange in
              let sigelts = FStar_Util.mk_ref [] in
              let register env2 lident def =
                let uu___2 =
                  FStar_TypeChecker_Util.mk_toplevel_definition env2 lident
                    def in
                match uu___2 with
                | (sigelt, fv) ->
                    let sigelt1 =
                      let uu___3 = sigelt in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (let uu___4 = sigelt.FStar_Syntax_Syntax.sigmeta in
                           {
                             FStar_Syntax_Syntax.sigmeta_active =
                               (uu___4.FStar_Syntax_Syntax.sigmeta_active);
                             FStar_Syntax_Syntax.sigmeta_fact_db_ids =
                               (uu___4.FStar_Syntax_Syntax.sigmeta_fact_db_ids);
                             FStar_Syntax_Syntax.sigmeta_admit = true
                           });
                        FStar_Syntax_Syntax.sigattrs =
                          (uu___3.FStar_Syntax_Syntax.sigattrs);
                        FStar_Syntax_Syntax.sigopts =
                          (uu___3.FStar_Syntax_Syntax.sigopts)
                      } in
                    ((let uu___4 =
                        let uu___5 = FStar_ST.op_Bang sigelts in sigelt1 ::
                          uu___5 in
                      FStar_ST.op_Colon_Equals sigelts uu___4);
                     fv) in
              let binders_of_list =
                FStar_List.map
                  (fun uu___2 ->
                     match uu___2 with
                     | (t, b) ->
                         let uu___3 = FStar_Syntax_Syntax.as_implicit b in
                         FStar_Syntax_Syntax.mk_binder_with_attrs t uu___3 []) in
              let mk_all_implicit =
                FStar_List.map
                  (fun t ->
                     let uu___2 = t in
                     let uu___3 = FStar_Syntax_Syntax.as_implicit true in
                     {
                       FStar_Syntax_Syntax.binder_bv =
                         (uu___2.FStar_Syntax_Syntax.binder_bv);
                       FStar_Syntax_Syntax.binder_qual = uu___3;
                       FStar_Syntax_Syntax.binder_attrs =
                         (uu___2.FStar_Syntax_Syntax.binder_attrs)
                     }) in
              let args_of_binders =
                FStar_List.map
                  (fun bv ->
                     let uu___2 =
                       FStar_Syntax_Syntax.bv_to_name
                         bv.FStar_Syntax_Syntax.binder_bv in
                     FStar_Syntax_Syntax.as_arg uu___2) in
              let uu___2 =
                let uu___3 =
                  let mk1 f =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let body =
                      let uu___4 =
                        let uu___5 = FStar_Syntax_Syntax.bv_to_name t in
                        f uu___5 in
                      FStar_Syntax_Util.arrow gamma uu___4 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStar_Syntax_Syntax.mk_binder a1 in
                        let uu___7 =
                          let uu___8 = FStar_Syntax_Syntax.mk_binder t in
                          [uu___8] in
                        uu___6 :: uu___7 in
                      FStar_List.append binders uu___5 in
                    FStar_Syntax_Util.abs uu___4 body
                      FStar_Pervasives_Native.None in
                  let uu___4 = mk1 FStar_Syntax_Syntax.mk_Total in
                  let uu___5 = mk1 FStar_Syntax_Syntax.mk_GTotal in
                  (uu___4, uu___5) in
                match uu___3 with
                | (ctx_def, gctx_def) ->
                    let ctx_lid = mk_lid "ctx" in
                    let ctx_fv = register env1 ctx_lid ctx_def in
                    let gctx_lid = mk_lid "gctx" in
                    let gctx_fv = register env1 gctx_lid gctx_def in
                    let mk_app fv t =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              FStar_List.map
                                (fun uu___8 ->
                                   match uu___8 with
                                   | { FStar_Syntax_Syntax.binder_bv = bv;
                                       FStar_Syntax_Syntax.binder_qual =
                                         uu___9;
                                       FStar_Syntax_Syntax.binder_attrs =
                                         uu___10;_}
                                       ->
                                       let uu___11 =
                                         FStar_Syntax_Syntax.bv_to_name bv in
                                       let uu___12 =
                                         FStar_Syntax_Syntax.as_implicit
                                           false in
                                       (uu___11, uu___12)) binders in
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  FStar_Syntax_Syntax.bv_to_name a1 in
                                let uu___11 =
                                  FStar_Syntax_Syntax.as_implicit false in
                                (uu___10, uu___11) in
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStar_Syntax_Syntax.as_implicit false in
                                  (t, uu___12) in
                                [uu___11] in
                              uu___9 :: uu___10 in
                            FStar_List.append uu___7 uu___8 in
                          (fv, uu___6) in
                        FStar_Syntax_Syntax.Tm_app uu___5 in
                      mk uu___4 in
                    (env1, (mk_app ctx_fv), (mk_app gctx_fv)) in
              match uu___2 with
              | (env2, mk_ctx, mk_gctx) ->
                  let c_pure =
                    let t =
                      FStar_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let x =
                      let uu___3 = FStar_Syntax_Syntax.bv_to_name t in
                      FStar_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu___3 in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu___5 in
                        FStar_Syntax_Util.residual_tot uu___4 in
                      FStar_Pervasives_Native.Some uu___3 in
                    let body =
                      let uu___3 = FStar_Syntax_Syntax.bv_to_name x in
                      FStar_Syntax_Util.abs gamma uu___3 ret in
                    let uu___3 =
                      let uu___4 = mk_all_implicit binders in
                      let uu___5 =
                        binders_of_list [(a1, true); (t, true); (x, false)] in
                      FStar_List.append uu___4 uu___5 in
                    FStar_Syntax_Util.abs uu___3 body ret in
                  let c_pure1 =
                    let uu___3 = mk_lid "pure" in register env2 uu___3 c_pure in
                  let c_app =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let l =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu___8 in
                              FStar_Syntax_Syntax.mk_binder uu___7 in
                            [uu___6] in
                          let uu___6 =
                            let uu___7 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.mk_GTotal uu___7 in
                          FStar_Syntax_Util.arrow uu___5 uu___6 in
                        mk_gctx uu___4 in
                      FStar_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu___3 in
                    let r =
                      let uu___3 =
                        let uu___4 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu___4 in
                      FStar_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu___3 in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu___5 in
                        FStar_Syntax_Util.residual_tot uu___4 in
                      FStar_Pervasives_Native.Some uu___3 in
                    let outer_body =
                      let gamma_as_args = args_of_binders gamma in
                      let inner_body =
                        let uu___3 = FStar_Syntax_Syntax.bv_to_name l in
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = FStar_Syntax_Syntax.bv_to_name r in
                                FStar_Syntax_Util.mk_app uu___8 gamma_as_args in
                              FStar_Syntax_Syntax.as_arg uu___7 in
                            [uu___6] in
                          FStar_List.append gamma_as_args uu___5 in
                        FStar_Syntax_Util.mk_app uu___3 uu___4 in
                      FStar_Syntax_Util.abs gamma inner_body ret in
                    let uu___3 =
                      let uu___4 = mk_all_implicit binders in
                      let uu___5 =
                        binders_of_list
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStar_List.append uu___4 uu___5 in
                    FStar_Syntax_Util.abs uu___3 outer_body ret in
                  let c_app1 =
                    let uu___3 = mk_lid "app" in register env2 uu___3 c_app in
                  let c_lift1 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu___5 in
                        [uu___4] in
                      let uu___4 =
                        let uu___5 = FStar_Syntax_Syntax.bv_to_name t2 in
                        FStar_Syntax_Syntax.mk_GTotal uu___5 in
                      FStar_Syntax_Util.arrow uu___3 uu___4 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu___3 =
                        let uu___4 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu___4 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu___3 in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu___5 in
                        FStar_Syntax_Util.residual_tot uu___4 in
                      FStar_Pervasives_Native.Some uu___3 in
                    let uu___3 =
                      let uu___4 = mk_all_implicit binders in
                      let uu___5 =
                        binders_of_list
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (f, false);
                          (a11, false)] in
                      FStar_List.append uu___4 uu___5 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  FStar_Syntax_Syntax.bv_to_name f in
                                [uu___10] in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu___9 in
                            FStar_Syntax_Util.mk_app c_pure1 uu___8 in
                          let uu___8 =
                            let uu___9 = FStar_Syntax_Syntax.bv_to_name a11 in
                            [uu___9] in
                          uu___7 :: uu___8 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu___6 in
                      FStar_Syntax_Util.mk_app c_app1 uu___5 in
                    FStar_Syntax_Util.abs uu___3 uu___4 ret in
                  let c_lift11 =
                    let uu___3 = mk_lid "lift1" in
                    register env2 uu___3 c_lift1 in
                  let c_lift2 =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t3 =
                      FStar_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu___5 in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = FStar_Syntax_Syntax.bv_to_name t2 in
                            FStar_Syntax_Syntax.null_binder uu___7 in
                          [uu___6] in
                        uu___4 :: uu___5 in
                      let uu___4 =
                        let uu___5 = FStar_Syntax_Syntax.bv_to_name t3 in
                        FStar_Syntax_Syntax.mk_GTotal uu___5 in
                      FStar_Syntax_Util.arrow uu___3 uu___4 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu___3 =
                        let uu___4 = FStar_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu___4 in
                      FStar_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu___3 in
                    let a2 =
                      let uu___3 =
                        let uu___4 = FStar_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu___4 in
                      FStar_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu___3 in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu___5 in
                        FStar_Syntax_Util.residual_tot uu___4 in
                      FStar_Pervasives_Native.Some uu___3 in
                    let uu___3 =
                      let uu___4 = mk_all_implicit binders in
                      let uu___5 =
                        binders_of_list
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (t3, true);
                          (f, false);
                          (a11, false);
                          (a2, false)] in
                      FStar_List.append uu___4 uu___5 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      let uu___13 =
                                        FStar_Syntax_Syntax.bv_to_name f in
                                      [uu___13] in
                                    FStar_List.map FStar_Syntax_Syntax.as_arg
                                      uu___12 in
                                  FStar_Syntax_Util.mk_app c_pure1 uu___11 in
                                let uu___11 =
                                  let uu___12 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  [uu___12] in
                                uu___10 :: uu___11 in
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                uu___9 in
                            FStar_Syntax_Util.mk_app c_app1 uu___8 in
                          let uu___8 =
                            let uu___9 = FStar_Syntax_Syntax.bv_to_name a2 in
                            [uu___9] in
                          uu___7 :: uu___8 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu___6 in
                      FStar_Syntax_Util.mk_app c_app1 uu___5 in
                    FStar_Syntax_Util.abs uu___3 uu___4 ret in
                  let c_lift21 =
                    let uu___3 = mk_lid "lift2" in
                    register env2 uu___3 c_lift2 in
                  let c_push =
                    let t1 =
                      FStar_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t2 =
                      FStar_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name t1 in
                          FStar_Syntax_Syntax.null_binder uu___5 in
                        [uu___4] in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStar_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu___6 in
                        FStar_Syntax_Syntax.mk_Total uu___5 in
                      FStar_Syntax_Util.arrow uu___3 uu___4 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  FStar_Syntax_Syntax.bv_to_name t1 in
                                FStar_Syntax_Syntax.null_binder uu___8 in
                              [uu___7] in
                            let uu___7 =
                              let uu___8 = FStar_Syntax_Syntax.bv_to_name t2 in
                              FStar_Syntax_Syntax.mk_GTotal uu___8 in
                            FStar_Syntax_Util.arrow uu___6 uu___7 in
                          mk_ctx uu___5 in
                        FStar_Syntax_Util.residual_tot uu___4 in
                      FStar_Pervasives_Native.Some uu___3 in
                    let e1 =
                      let uu___3 = FStar_Syntax_Syntax.bv_to_name t1 in
                      FStar_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu___3 in
                    let body =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.mk_binder e1 in
                          [uu___5] in
                        FStar_List.append gamma uu___4 in
                      let uu___4 =
                        let uu___5 = FStar_Syntax_Syntax.bv_to_name f in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = FStar_Syntax_Syntax.bv_to_name e1 in
                            FStar_Syntax_Syntax.as_arg uu___8 in
                          let uu___8 = args_of_binders gamma in uu___7 ::
                            uu___8 in
                        FStar_Syntax_Util.mk_app uu___5 uu___6 in
                      FStar_Syntax_Util.abs uu___3 uu___4 ret in
                    let uu___3 =
                      let uu___4 = mk_all_implicit binders in
                      let uu___5 =
                        binders_of_list
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStar_List.append uu___4 uu___5 in
                    FStar_Syntax_Util.abs uu___3 body ret in
                  let c_push1 =
                    let uu___3 = mk_lid "push" in register env2 uu___3 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStar_List.length binders) > Prims.int_zero
                    then
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = args_of_binders binders in (c, uu___5) in
                        FStar_Syntax_Syntax.Tm_app uu___4 in
                      mk uu___3
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.null_binder wp_a1 in
                          let uu___6 =
                            let uu___7 =
                              FStar_Syntax_Syntax.null_binder wp_a1 in
                            [uu___7] in
                          uu___5 :: uu___6 in
                        let uu___5 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                        FStar_Syntax_Util.arrow uu___4 uu___5 in
                      FStar_Syntax_Syntax.mk_Total uu___3 in
                    let c =
                      FStar_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let uu___3 =
                      let uu___4 =
                        FStar_Syntax_Syntax.binders_of_list [a1; c] in
                      FStar_List.append binders uu___4 in
                    let uu___4 =
                      let l_ite =
                        FStar_Syntax_Syntax.fvar FStar_Parser_Const.ite_lid
                          (FStar_Syntax_Syntax.Delta_constant_at_level
                             (Prims.of_int (2))) FStar_Pervasives_Native.None in
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_Syntax_Syntax.bv_to_name c in
                                  FStar_Syntax_Syntax.as_arg uu___11 in
                                [uu___10] in
                              FStar_Syntax_Util.mk_app l_ite uu___9 in
                            [uu___8] in
                          FStar_List.map FStar_Syntax_Syntax.as_arg uu___7 in
                        FStar_Syntax_Util.mk_app c_lift21 uu___6 in
                      FStar_Syntax_Util.ascribe uu___5
                        ((FStar_Pervasives.Inr result_comp),
                          FStar_Pervasives_Native.None) in
                    FStar_Syntax_Util.abs uu___3 uu___4
                      (FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.residual_comp_of_comp result_comp)) in
                  let wp_if_then_else1 =
                    let uu___3 = mk_lid "wp_if_then_else" in
                    register env2 uu___3 wp_if_then_else in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1 in
                  let wp_close =
                    let b =
                      FStar_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStar_Syntax_Util.ktype in
                    let t_f =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name b in
                          FStar_Syntax_Syntax.null_binder uu___5 in
                        [uu___4] in
                      let uu___4 = FStar_Syntax_Syntax.mk_Total wp_a1 in
                      FStar_Syntax_Util.arrow uu___3 uu___4 in
                    let f =
                      FStar_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_List.map FStar_Syntax_Syntax.as_arg
                                [FStar_Syntax_Util.tforall] in
                            FStar_Syntax_Util.mk_app c_pure1 uu___6 in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    FStar_Syntax_Syntax.bv_to_name f in
                                  [uu___10] in
                                FStar_List.map FStar_Syntax_Syntax.as_arg
                                  uu___9 in
                              FStar_Syntax_Util.mk_app c_push1 uu___8 in
                            [uu___7] in
                          uu___5 :: uu___6 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu___4 in
                      FStar_Syntax_Util.mk_app c_app1 uu___3 in
                    let uu___3 =
                      let uu___4 =
                        FStar_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStar_List.append binders uu___4 in
                    FStar_Syntax_Util.abs uu___3 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu___3 = mk_lid "wp_close" in
                    register env2 uu___3 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStar_Syntax_Syntax.mk_GTotal
                            FStar_Syntax_Util.ktype in
                        FStar_All.pipe_left
                          FStar_TypeChecker_Common.lcomp_of_comp uu___5 in
                      FStar_TypeChecker_Common.residual_comp_of_lcomp uu___4 in
                    FStar_Pervasives_Native.Some uu___3 in
                  let mk_forall x body =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 = FStar_Syntax_Syntax.mk_binder x in
                                [uu___9] in
                              FStar_Syntax_Util.abs uu___8 body ret_tot_type in
                            FStar_Syntax_Syntax.as_arg uu___7 in
                          [uu___6] in
                        (FStar_Syntax_Util.tforall, uu___5) in
                      FStar_Syntax_Syntax.Tm_app uu___4 in
                    FStar_Syntax_Syntax.mk uu___3 FStar_Range.dummyRange in
                  let rec is_discrete t =
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Subst.compress t in
                      uu___4.FStar_Syntax_Syntax.n in
                    match uu___3 with
                    | FStar_Syntax_Syntax.Tm_type uu___4 -> false
                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                        (FStar_List.for_all
                           (fun uu___4 ->
                              match uu___4 with
                              | { FStar_Syntax_Syntax.binder_bv = b;
                                  FStar_Syntax_Syntax.binder_qual = uu___5;
                                  FStar_Syntax_Syntax.binder_attrs = uu___6;_}
                                  -> is_discrete b.FStar_Syntax_Syntax.sort)
                           bs)
                          && (is_discrete (FStar_Syntax_Util.comp_result c))
                    | uu___4 -> true in
                  let rec is_monotonic t =
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Subst.compress t in
                      uu___4.FStar_Syntax_Syntax.n in
                    match uu___3 with
                    | FStar_Syntax_Syntax.Tm_type uu___4 -> true
                    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                        (FStar_List.for_all
                           (fun uu___4 ->
                              match uu___4 with
                              | { FStar_Syntax_Syntax.binder_bv = b;
                                  FStar_Syntax_Syntax.binder_qual = uu___5;
                                  FStar_Syntax_Syntax.binder_attrs = uu___6;_}
                                  -> is_discrete b.FStar_Syntax_Syntax.sort)
                           bs)
                          && (is_monotonic (FStar_Syntax_Util.comp_result c))
                    | uu___4 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.Beta;
                        FStar_TypeChecker_Env.Eager_unfolding;
                        FStar_TypeChecker_Env.UnfoldUntil
                          FStar_Syntax_Syntax.delta_constant] env2 t in
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Subst.compress t1 in
                      uu___4.FStar_Syntax_Syntax.n in
                    match uu___3 with
                    | FStar_Syntax_Syntax.Tm_type uu___4 -> rel x y
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],
                         {
                           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                             (b, uu___4);
                           FStar_Syntax_Syntax.pos = uu___5;
                           FStar_Syntax_Syntax.vars = uu___6;_})
                        ->
                        let a2 =
                          (binder.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                        let uu___7 = (is_monotonic a2) || (is_monotonic b) in
                        if uu___7
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu___11 in
                                [uu___10] in
                              FStar_Syntax_Util.mk_app x uu___9 in
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu___12 in
                                [uu___11] in
                              FStar_Syntax_Util.mk_app y uu___10 in
                            mk_rel1 b uu___8 uu___9 in
                          mk_forall a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu___9 =
                               let uu___10 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu___11 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu___10 uu___11 in
                             let uu___10 =
                               let uu___11 =
                                 let uu___12 =
                                   let uu___13 =
                                     let uu___14 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu___14 in
                                   [uu___13] in
                                 FStar_Syntax_Util.mk_app x uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   let uu___14 =
                                     let uu___15 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu___15 in
                                   [uu___14] in
                                 FStar_Syntax_Util.mk_app y uu___13 in
                               mk_rel1 b uu___11 uu___12 in
                             FStar_Syntax_Util.mk_imp uu___9 uu___10 in
                           let uu___9 = mk_forall a21 body in
                           mk_forall a11 uu___9)
                    | FStar_Syntax_Syntax.Tm_arrow
                        (binder::[],
                         {
                           FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                             (b, uu___4);
                           FStar_Syntax_Syntax.pos = uu___5;
                           FStar_Syntax_Syntax.vars = uu___6;_})
                        ->
                        let a2 =
                          (binder.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                        let uu___7 = (is_monotonic a2) || (is_monotonic b) in
                        if uu___7
                        then
                          let a11 =
                            FStar_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu___11 in
                                [uu___10] in
                              FStar_Syntax_Util.mk_app x uu___9 in
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStar_Syntax_Syntax.bv_to_name a11 in
                                  FStar_Syntax_Syntax.as_arg uu___12 in
                                [uu___11] in
                              FStar_Syntax_Util.mk_app y uu___10 in
                            mk_rel1 b uu___8 uu___9 in
                          mk_forall a11 body
                        else
                          (let a11 =
                             FStar_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStar_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu___9 =
                               let uu___10 =
                                 FStar_Syntax_Syntax.bv_to_name a11 in
                               let uu___11 =
                                 FStar_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu___10 uu___11 in
                             let uu___10 =
                               let uu___11 =
                                 let uu___12 =
                                   let uu___13 =
                                     let uu___14 =
                                       FStar_Syntax_Syntax.bv_to_name a11 in
                                     FStar_Syntax_Syntax.as_arg uu___14 in
                                   [uu___13] in
                                 FStar_Syntax_Util.mk_app x uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   let uu___14 =
                                     let uu___15 =
                                       FStar_Syntax_Syntax.bv_to_name a21 in
                                     FStar_Syntax_Syntax.as_arg uu___15 in
                                   [uu___14] in
                                 FStar_Syntax_Util.mk_app y uu___13 in
                               mk_rel1 b uu___11 uu___12 in
                             FStar_Syntax_Util.mk_imp uu___9 uu___10 in
                           let uu___9 = mk_forall a21 body in
                           mk_forall a11 uu___9)
                    | FStar_Syntax_Syntax.Tm_arrow (binder::binders1, comp)
                        ->
                        let t2 =
                          let uu___4 = t1 in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  FStar_Syntax_Util.arrow binders1 comp in
                                FStar_Syntax_Syntax.mk_Total uu___8 in
                              ([binder], uu___7) in
                            FStar_Syntax_Syntax.Tm_arrow uu___6 in
                          {
                            FStar_Syntax_Syntax.n = uu___5;
                            FStar_Syntax_Syntax.pos =
                              (uu___4.FStar_Syntax_Syntax.pos);
                            FStar_Syntax_Syntax.vars =
                              (uu___4.FStar_Syntax_Syntax.vars)
                          } in
                        mk_rel1 t2 x y
                    | FStar_Syntax_Syntax.Tm_arrow ([], uu___4) ->
                        failwith "impossible: arrow with empty binders"
                    | uu___4 -> FStar_Syntax_Util.mk_untyped_eq2 x y in
                  let stronger =
                    let wp1 =
                      FStar_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1 in
                    let wp2 =
                      FStar_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1 in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.UnfoldUntil
                            FStar_Syntax_Syntax.delta_constant] env2 t in
                      let uu___3 =
                        let uu___4 = FStar_Syntax_Subst.compress t1 in
                        uu___4.FStar_Syntax_Syntax.n in
                      match uu___3 with
                      | FStar_Syntax_Syntax.Tm_type uu___4 ->
                          FStar_Syntax_Util.mk_imp x y
                      | FStar_Syntax_Syntax.Tm_app (head, args) when
                          let uu___4 = FStar_Syntax_Subst.compress head in
                          FStar_Syntax_Util.is_tuple_constructor uu___4 ->
                          let project i tuple =
                            let projector =
                              let uu___4 =
                                let uu___5 =
                                  FStar_Parser_Const.mk_tuple_data_lid
                                    (FStar_List.length args)
                                    FStar_Range.dummyRange in
                                FStar_TypeChecker_Env.lookup_projector env2
                                  uu___5 i in
                              FStar_Syntax_Syntax.fvar uu___4
                                (FStar_Syntax_Syntax.Delta_constant_at_level
                                   Prims.int_one)
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu___4 =
                            let uu___5 =
                              FStar_List.mapi
                                (fun i ->
                                   fun uu___6 ->
                                     match uu___6 with
                                     | (t2, q) ->
                                         let uu___7 = project i x in
                                         let uu___8 = project i y in
                                         mk_stronger t2 uu___7 uu___8) args in
                            match uu___5 with
                            | [] ->
                                failwith
                                  "Impossible: empty application when creating stronger relation in DM4F"
                            | rel0::rels -> (rel0, rels) in
                          (match uu___4 with
                           | (rel0, rels) ->
                               FStar_List.fold_left FStar_Syntax_Util.mk_conj
                                 rel0 rels)
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,
                           {
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.GTotal (b, uu___4);
                             FStar_Syntax_Syntax.pos = uu___5;
                             FStar_Syntax_Syntax.vars = uu___6;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i ->
                                 fun uu___7 ->
                                   match uu___7 with
                                   | { FStar_Syntax_Syntax.binder_bv = bv;
                                       FStar_Syntax_Syntax.binder_qual = q;
                                       FStar_Syntax_Syntax.binder_attrs =
                                         uu___8;_}
                                       ->
                                       let uu___9 =
                                         let uu___10 =
                                           FStar_Util.string_of_int i in
                                         Prims.op_Hat "a" uu___10 in
                                       FStar_Syntax_Syntax.gen_bv uu___9
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai ->
                                 let uu___7 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu___7) bvs in
                          let body =
                            let uu___7 = FStar_Syntax_Util.mk_app x args in
                            let uu___8 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu___7 uu___8 in
                          FStar_List.fold_right
                            (fun bv -> fun body1 -> mk_forall bv body1) bvs
                            body
                      | FStar_Syntax_Syntax.Tm_arrow
                          (binders1,
                           {
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Total (b, uu___4);
                             FStar_Syntax_Syntax.pos = uu___5;
                             FStar_Syntax_Syntax.vars = uu___6;_})
                          ->
                          let bvs =
                            FStar_List.mapi
                              (fun i ->
                                 fun uu___7 ->
                                   match uu___7 with
                                   | { FStar_Syntax_Syntax.binder_bv = bv;
                                       FStar_Syntax_Syntax.binder_qual = q;
                                       FStar_Syntax_Syntax.binder_attrs =
                                         uu___8;_}
                                       ->
                                       let uu___9 =
                                         let uu___10 =
                                           FStar_Util.string_of_int i in
                                         Prims.op_Hat "a" uu___10 in
                                       FStar_Syntax_Syntax.gen_bv uu___9
                                         FStar_Pervasives_Native.None
                                         bv.FStar_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStar_List.map
                              (fun ai ->
                                 let uu___7 =
                                   FStar_Syntax_Syntax.bv_to_name ai in
                                 FStar_Syntax_Syntax.as_arg uu___7) bvs in
                          let body =
                            let uu___7 = FStar_Syntax_Util.mk_app x args in
                            let uu___8 = FStar_Syntax_Util.mk_app y args in
                            mk_stronger b uu___7 uu___8 in
                          FStar_List.fold_right
                            (fun bv -> fun body1 -> mk_forall bv body1) bvs
                            body
                      | uu___4 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu___3 = FStar_Syntax_Util.unascribe wp_a1 in
                      let uu___4 = FStar_Syntax_Syntax.bv_to_name wp1 in
                      let uu___5 = FStar_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu___3 uu___4 uu___5 in
                    let uu___3 =
                      let uu___4 =
                        binders_of_list
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStar_List.append binders uu___4 in
                    FStar_Syntax_Util.abs uu___3 body ret_tot_type in
                  let stronger1 =
                    let uu___3 = mk_lid "stronger" in
                    register env2 uu___3 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let ite_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu___3 = FStar_Util.prefix gamma in
                    match uu___3 with
                    | (wp_args, post) ->
                        let k =
                          FStar_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (post.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                        let equiv =
                          let k_tm = FStar_Syntax_Syntax.bv_to_name k in
                          let eq =
                            let uu___4 =
                              FStar_Syntax_Syntax.bv_to_name
                                post.FStar_Syntax_Syntax.binder_bv in
                            mk_rel FStar_Syntax_Util.mk_iff
                              k.FStar_Syntax_Syntax.sort k_tm uu___4 in
                          let uu___4 =
                            FStar_Syntax_Util.destruct_typ_as_formula eq in
                          match uu___4 with
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.QAll (binders1, [], body))
                              ->
                              let k_app =
                                let uu___5 = args_of_binders binders1 in
                                FStar_Syntax_Util.mk_app k_tm uu___5 in
                              let guard_free =
                                let uu___5 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.guard_free
                                    FStar_Syntax_Syntax.delta_constant
                                    FStar_Pervasives_Native.None in
                                FStar_Syntax_Syntax.fv_to_tm uu___5 in
                              let pat =
                                let uu___5 =
                                  let uu___6 =
                                    FStar_Syntax_Syntax.as_arg k_app in
                                  [uu___6] in
                                FStar_Syntax_Util.mk_app guard_free uu___5 in
                              let pattern_guarded_body =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 =
                                      let uu___8 =
                                        let uu___9 =
                                          FStar_Syntax_Syntax.binders_to_names
                                            binders1 in
                                        let uu___10 =
                                          let uu___11 =
                                            let uu___12 =
                                              FStar_Syntax_Syntax.as_arg pat in
                                            [uu___12] in
                                          [uu___11] in
                                        (uu___9, uu___10) in
                                      FStar_Syntax_Syntax.Meta_pattern uu___8 in
                                    (body, uu___7) in
                                  FStar_Syntax_Syntax.Tm_meta uu___6 in
                                mk uu___5 in
                              FStar_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu___5 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Syntax.bv_to_name wp in
                                let uu___8 =
                                  let uu___9 = args_of_binders wp_args in
                                  let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        FStar_Syntax_Syntax.bv_to_name k in
                                      FStar_Syntax_Syntax.as_arg uu___12 in
                                    [uu___11] in
                                  FStar_List.append uu___9 uu___10 in
                                FStar_Syntax_Util.mk_app uu___7 uu___8 in
                              FStar_Syntax_Util.mk_imp equiv uu___6 in
                            FStar_Syntax_Util.mk_forall_no_univ k uu___5 in
                          FStar_Syntax_Util.abs gamma uu___4 ret_gtot_type in
                        let uu___4 =
                          let uu___5 =
                            FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStar_List.append binders uu___5 in
                        FStar_Syntax_Util.abs uu___4 body ret_gtot_type in
                  let ite_wp1 =
                    let uu___3 = mk_lid "ite_wp" in
                    register env2 uu___3 ite_wp in
                  let ite_wp2 = mk_generic_app ite_wp1 in
                  let null_wp =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu___3 = FStar_Util.prefix gamma in
                    match uu___3 with
                    | (wp_args, post) ->
                        let x =
                          FStar_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStar_Syntax_Syntax.tun in
                        let body =
                          let uu___4 =
                            let uu___5 =
                              FStar_All.pipe_left
                                FStar_Syntax_Syntax.bv_to_name
                                post.FStar_Syntax_Syntax.binder_bv in
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = FStar_Syntax_Syntax.bv_to_name x in
                                FStar_Syntax_Syntax.as_arg uu___8 in
                              [uu___7] in
                            FStar_Syntax_Util.mk_app uu___5 uu___6 in
                          FStar_Syntax_Util.mk_forall_no_univ x uu___4 in
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_Syntax_Syntax.binders_of_list [a1] in
                            FStar_List.append uu___6 gamma in
                          FStar_List.append binders uu___5 in
                        FStar_Syntax_Util.abs uu___4 body ret_gtot_type in
                  let null_wp1 =
                    let uu___3 = mk_lid "null_wp" in
                    register env2 uu___3 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStar_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Syntax.bv_to_name a1 in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    FStar_Syntax_Syntax.bv_to_name a1 in
                                  FStar_Syntax_Syntax.as_arg uu___10 in
                                [uu___9] in
                              FStar_Syntax_Util.mk_app null_wp2 uu___8 in
                            let uu___8 =
                              let uu___9 = FStar_Syntax_Syntax.bv_to_name wp in
                              [uu___9] in
                            uu___7 :: uu___8 in
                          uu___5 :: uu___6 in
                        FStar_List.map FStar_Syntax_Syntax.as_arg uu___4 in
                      FStar_Syntax_Util.mk_app stronger2 uu___3 in
                    let uu___3 =
                      let uu___4 =
                        FStar_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStar_List.append binders uu___4 in
                    FStar_Syntax_Util.abs uu___3 body ret_tot_type in
                  let wp_trivial1 =
                    let uu___3 = mk_lid "wp_trivial" in
                    register env2 uu___3 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu___4 =
                      FStar_TypeChecker_Env.debug env2
                        (FStar_Options.Other "ED") in
                    if uu___4 then d "End Dijkstra monads for free" else ());
                   (let c = FStar_Syntax_Subst.close binders in
                    let ed_combs =
                      match ed.FStar_Syntax_Syntax.combinators with
                      | FStar_Syntax_Syntax.DM4F_eff combs ->
                          let uu___4 =
                            let uu___5 = combs in
                            let uu___6 =
                              let uu___7 = c stronger2 in ([], uu___7) in
                            let uu___7 =
                              let uu___8 = c wp_if_then_else2 in ([], uu___8) in
                            let uu___8 =
                              let uu___9 = c ite_wp2 in ([], uu___9) in
                            let uu___9 =
                              let uu___10 = c wp_close2 in ([], uu___10) in
                            let uu___10 =
                              let uu___11 = c wp_trivial2 in ([], uu___11) in
                            {
                              FStar_Syntax_Syntax.ret_wp =
                                (uu___5.FStar_Syntax_Syntax.ret_wp);
                              FStar_Syntax_Syntax.bind_wp =
                                (uu___5.FStar_Syntax_Syntax.bind_wp);
                              FStar_Syntax_Syntax.stronger = uu___6;
                              FStar_Syntax_Syntax.if_then_else = uu___7;
                              FStar_Syntax_Syntax.ite_wp = uu___8;
                              FStar_Syntax_Syntax.close_wp = uu___9;
                              FStar_Syntax_Syntax.trivial = uu___10;
                              FStar_Syntax_Syntax.repr =
                                (uu___5.FStar_Syntax_Syntax.repr);
                              FStar_Syntax_Syntax.return_repr =
                                (uu___5.FStar_Syntax_Syntax.return_repr);
                              FStar_Syntax_Syntax.bind_repr =
                                (uu___5.FStar_Syntax_Syntax.bind_repr)
                            } in
                          FStar_Syntax_Syntax.DM4F_eff uu___4
                      | uu___4 ->
                          failwith
                            "Impossible! For a DM4F effect combinators must be in DM4f_eff" in
                    let uu___4 =
                      let uu___5 = FStar_ST.op_Bang sigelts in
                      FStar_List.rev uu___5 in
                    (uu___4,
                      (let uu___5 = ed in
                       {
                         FStar_Syntax_Syntax.mname =
                           (uu___5.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___5.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.univs =
                           (uu___5.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___5.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature =
                           (uu___5.FStar_Syntax_Syntax.signature);
                         FStar_Syntax_Syntax.combinators = ed_combs;
                         FStar_Syntax_Syntax.actions =
                           (uu___5.FStar_Syntax_Syntax.actions);
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___5.FStar_Syntax_Syntax.eff_attrs)
                       }))))))
type env_ = env
let (get_env : env -> FStar_TypeChecker_Env.env) = fun env1 -> env1.tcenv
let (set_env : env -> FStar_TypeChecker_Env.env -> env) =
  fun dmff_env ->
    fun env' ->
      let uu___ = dmff_env in
      { tcenv = env'; subst = (uu___.subst); tc_const = (uu___.tc_const) }
type nm =
  | N of FStar_Syntax_Syntax.typ 
  | M of FStar_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee -> match projectee with | N _0 -> true | uu___ -> false
let (__proj__N__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | N _0 -> _0
let (uu___is_M : nm -> Prims.bool) =
  fun projectee -> match projectee with | M _0 -> true | uu___ -> false
let (__proj__M__item___0 : nm -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | M _0 -> _0
type nm_ = nm
let (nm_of_comp : FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> nm)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu___) -> N t
    | FStar_Syntax_Syntax.Comp c1 when
        FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
          (FStar_Util.for_some
             (fun uu___ ->
                match uu___ with
                | FStar_Syntax_Syntax.CPS -> true
                | uu___1 -> false))
        -> M (c1.FStar_Syntax_Syntax.result_typ)
    | uu___ ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.comp_to_string c in
            FStar_Util.format1 "[nm_of_comp]: unexpected computation type %s"
              uu___3 in
          (FStar_Errors.Error_UnexpectedDM4FType, uu___2) in
        FStar_Errors.raise_error uu___1 c.FStar_Syntax_Syntax.pos
let (string_of_nm : nm -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | N t ->
        let uu___1 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "N[%s]" uu___1
    | M t ->
        let uu___1 = FStar_Syntax_Print.term_to_string t in
        FStar_Util.format1 "M[%s]" uu___1
let (is_monadic_arrow : FStar_Syntax_Syntax.term' -> nm) =
  fun n ->
    match n with
    | FStar_Syntax_Syntax.Tm_arrow (uu___, c) -> nm_of_comp c
    | uu___ -> failwith "unexpected_argument: [is_monadic_arrow]"
let (is_monadic_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    let uu___ = nm_of_comp c in
    match uu___ with | M uu___1 -> true | N uu___1 -> false
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Not_found -> true | uu___ -> false
let (double_star : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ) =
  fun typ ->
    let star_once typ1 =
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu___2 in
        [uu___1] in
      let uu___1 = FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
      FStar_Syntax_Util.arrow uu___ uu___1 in
    let uu___ = FStar_All.pipe_right typ star_once in
    FStar_All.pipe_left star_once uu___
let rec (mk_star_to_type :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun mk ->
    fun env1 ->
      fun a ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = star_type' env1 a in
                  FStar_Syntax_Syntax.null_bv uu___5 in
                let uu___5 = FStar_Syntax_Syntax.as_implicit false in
                FStar_Syntax_Syntax.mk_binder_with_attrs uu___4 uu___5 [] in
              [uu___3] in
            let uu___3 =
              FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0 in
            (uu___2, uu___3) in
          FStar_Syntax_Syntax.Tm_arrow uu___1 in
        mk uu___
and (star_type' :
  env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk in
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (binders, uu___) ->
          let binders1 =
            FStar_List.map
              (fun b ->
                 let uu___1 = b in
                 let uu___2 =
                   let uu___3 = b.FStar_Syntax_Syntax.binder_bv in
                   let uu___4 =
                     star_type' env1
                       (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = uu___4
                   } in
                 {
                   FStar_Syntax_Syntax.binder_bv = uu___2;
                   FStar_Syntax_Syntax.binder_qual =
                     (uu___1.FStar_Syntax_Syntax.binder_qual);
                   FStar_Syntax_Syntax.binder_attrs =
                     (uu___1.FStar_Syntax_Syntax.binder_attrs)
                 }) binders in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow
               (uu___1,
                {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                    (hn, uu___2);
                  FStar_Syntax_Syntax.pos = uu___3;
                  FStar_Syntax_Syntax.vars = uu___4;_})
               ->
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = star_type' env1 hn in
                     FStar_Syntax_Syntax.mk_GTotal uu___8 in
                   (binders1, uu___7) in
                 FStar_Syntax_Syntax.Tm_arrow uu___6 in
               mk uu___5
           | uu___1 ->
               let uu___2 = is_monadic_arrow t1.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | N hn ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = star_type' env1 hn in
                          FStar_Syntax_Syntax.mk_Total uu___6 in
                        (binders1, uu___5) in
                      FStar_Syntax_Syntax.Tm_arrow uu___4 in
                    mk uu___3
                | M a ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 = mk_star_to_type1 env1 a in
                                FStar_Syntax_Syntax.null_bv uu___9 in
                              let uu___9 =
                                FStar_Syntax_Syntax.as_implicit false in
                              FStar_Syntax_Syntax.mk_binder_with_attrs uu___8
                                uu___9 [] in
                            [uu___7] in
                          FStar_List.append binders1 uu___6 in
                        let uu___6 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        (uu___5, uu___6) in
                      FStar_Syntax_Syntax.Tm_arrow uu___4 in
                    mk uu___3))
      | FStar_Syntax_Syntax.Tm_app (head, args) ->
          let debug t2 s =
            let string_of_set f s1 =
              let elts = FStar_Util.set_elements s1 in
              match elts with
              | [] -> "{}"
              | x::xs ->
                  let strb = FStar_Util.new_string_builder () in
                  (FStar_Util.string_builder_append strb "{";
                   (let uu___2 = f x in
                    FStar_Util.string_builder_append strb uu___2);
                   FStar_List.iter
                     (fun x1 ->
                        FStar_Util.string_builder_append strb ", ";
                        (let uu___4 = f x1 in
                         FStar_Util.string_builder_append strb uu___4)) xs;
                   FStar_Util.string_builder_append strb "}";
                   FStar_Util.string_of_string_builder strb) in
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.term_to_string t2 in
                let uu___3 = string_of_set FStar_Syntax_Print.bv_to_string s in
                FStar_Util.format2 "Dependency found in term %s : %s" uu___2
                  uu___3 in
              (FStar_Errors.Warning_DependencyFound, uu___1) in
            FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu___ in
          let rec is_non_dependent_arrow ty n =
            let uu___ =
              let uu___1 = FStar_Syntax_Subst.compress ty in
              uu___1.FStar_Syntax_Syntax.n in
            match uu___ with
            | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
                let uu___1 =
                  let uu___2 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                  Prims.op_Negation uu___2 in
                if uu___1
                then false
                else
                  (try
                     (fun uu___3 ->
                        match () with
                        | () ->
                            let non_dependent_or_raise s ty1 =
                              let sinter =
                                let uu___4 = FStar_Syntax_Free.names ty1 in
                                FStar_Util.set_intersect uu___4 s in
                              let uu___4 =
                                let uu___5 = FStar_Util.set_is_empty sinter in
                                Prims.op_Negation uu___5 in
                              if uu___4
                              then
                                (debug ty1 sinter; FStar_Exn.raise Not_found)
                              else () in
                            let uu___4 =
                              FStar_Syntax_Subst.open_comp binders c in
                            (match uu___4 with
                             | (binders1, c1) ->
                                 let s =
                                   FStar_List.fold_left
                                     (fun s1 ->
                                        fun uu___5 ->
                                          match uu___5 with
                                          | {
                                              FStar_Syntax_Syntax.binder_bv =
                                                bv;
                                              FStar_Syntax_Syntax.binder_qual
                                                = uu___6;
                                              FStar_Syntax_Syntax.binder_attrs
                                                = uu___7;_}
                                              ->
                                              (non_dependent_or_raise s1
                                                 bv.FStar_Syntax_Syntax.sort;
                                               FStar_Util.set_add bv s1))
                                     FStar_Syntax_Syntax.no_names binders1 in
                                 let ct = FStar_Syntax_Util.comp_result c1 in
                                 (non_dependent_or_raise s ct;
                                  (let k = n - (FStar_List.length binders1) in
                                   if k > Prims.int_zero
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found -> false)
            | uu___1 ->
                ((let uu___3 =
                    let uu___4 =
                      let uu___5 = FStar_Syntax_Print.term_to_string ty in
                      FStar_Util.format1 "Not a dependent arrow : %s" uu___5 in
                    (FStar_Errors.Warning_NotDependentArrow, uu___4) in
                  FStar_Errors.log_issue ty.FStar_Syntax_Syntax.pos uu___3);
                 false) in
          let rec is_valid_application head1 =
            let uu___ =
              let uu___1 = FStar_Syntax_Subst.compress head1 in
              uu___1.FStar_Syntax_Syntax.n in
            match uu___ with
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
                  (let uu___1 = FStar_Syntax_Subst.compress head1 in
                   FStar_Syntax_Util.is_tuple_constructor uu___1)
                -> true
            | FStar_Syntax_Syntax.Tm_fvar fv ->
                let uu___1 =
                  FStar_TypeChecker_Env.lookup_lid env1.tcenv
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                (match uu___1 with
                 | ((uu___2, ty), uu___3) ->
                     let uu___4 =
                       is_non_dependent_arrow ty (FStar_List.length args) in
                     if uu___4
                     then
                       let res =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Env.EraseUniverses;
                           FStar_TypeChecker_Env.Inlining;
                           FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant] env1.tcenv
                           t1 in
                       let uu___5 =
                         let uu___6 = FStar_Syntax_Subst.compress res in
                         uu___6.FStar_Syntax_Syntax.n in
                       (match uu___5 with
                        | FStar_Syntax_Syntax.Tm_app uu___6 -> true
                        | uu___6 ->
                            ((let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  FStar_Util.format1
                                    "Got a term which might be a non-dependent user-defined data-type %s\n"
                                    uu___10 in
                                (FStar_Errors.Warning_NondependentUserDefinedDataType,
                                  uu___9) in
                              FStar_Errors.log_issue
                                head1.FStar_Syntax_Syntax.pos uu___8);
                             false))
                     else false)
            | FStar_Syntax_Syntax.Tm_bvar uu___1 -> true
            | FStar_Syntax_Syntax.Tm_name uu___1 -> true
            | FStar_Syntax_Syntax.Tm_uinst (t2, uu___1) ->
                is_valid_application t2
            | uu___1 -> false in
          let uu___ = is_valid_application head in
          if uu___
          then
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStar_List.map
                    (fun uu___4 ->
                       match uu___4 with
                       | (t2, qual) ->
                           let uu___5 = star_type' env1 t2 in (uu___5, qual))
                    args in
                (head, uu___3) in
              FStar_Syntax_Syntax.Tm_app uu___2 in
            mk uu___1
          else
            (let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Syntax_Print.term_to_string t1 in
                 FStar_Util.format1
                   "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                   uu___4 in
               (FStar_Errors.Fatal_WrongTerm, uu___3) in
             FStar_Errors.raise_err uu___2)
      | FStar_Syntax_Syntax.Tm_bvar uu___ -> t1
      | FStar_Syntax_Syntax.Tm_name uu___ -> t1
      | FStar_Syntax_Syntax.Tm_type uu___ -> t1
      | FStar_Syntax_Syntax.Tm_fvar uu___ -> t1
      | FStar_Syntax_Syntax.Tm_abs (binders, repr, something) ->
          let uu___ = FStar_Syntax_Subst.open_term binders repr in
          (match uu___ with
           | (binders1, repr1) ->
               let env2 =
                 let uu___1 = env1 in
                 let uu___2 =
                   FStar_TypeChecker_Env.push_binders env1.tcenv binders1 in
                 {
                   tcenv = uu___2;
                   subst = (uu___1.subst);
                   tc_const = (uu___1.tc_const)
                 } in
               let repr2 = star_type' env2 repr1 in
               FStar_Syntax_Util.abs binders1 repr2 something)
      | FStar_Syntax_Syntax.Tm_refine (x, t2) when false ->
          let x1 = FStar_Syntax_Syntax.freshen_bv x in
          let sort = star_type' env1 x1.FStar_Syntax_Syntax.sort in
          let subst = [FStar_Syntax_Syntax.DB (Prims.int_zero, x1)] in
          let t3 = FStar_Syntax_Subst.subst subst t2 in
          let t4 = star_type' env1 t3 in
          let subst1 = [FStar_Syntax_Syntax.NM (x1, Prims.int_zero)] in
          let t5 = FStar_Syntax_Subst.subst subst1 t4 in
          mk
            (FStar_Syntax_Syntax.Tm_refine
               ((let uu___ = x1 in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = sort
                 }), t5))
      | FStar_Syntax_Syntax.Tm_meta (t2, m) ->
          let uu___ =
            let uu___1 = let uu___2 = star_type' env1 t2 in (uu___2, m) in
            FStar_Syntax_Syntax.Tm_meta uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_ascribed
          (e, (FStar_Pervasives.Inl t2, FStar_Pervasives_Native.None),
           something)
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = star_type' env1 e in
              let uu___3 =
                let uu___4 =
                  let uu___5 = star_type' env1 t2 in
                  FStar_Pervasives.Inl uu___5 in
                (uu___4, FStar_Pervasives_Native.None) in
              (uu___2, uu___3, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_ascribed
          (e, (FStar_Pervasives.Inr c, FStar_Pervasives_Native.None),
           something)
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = star_type' env1 e in
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    star_type' env1 (FStar_Syntax_Util.comp_result c) in
                  FStar_Pervasives.Inl uu___5 in
                (uu___4, FStar_Pervasives_Native.None) in
              (uu___2, uu___3, something) in
            FStar_Syntax_Syntax.Tm_ascribed uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu___, (uu___1, FStar_Pervasives_Native.Some uu___2), uu___3) ->
          let uu___4 =
            let uu___5 =
              let uu___6 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Ascriptions with tactics are outside of the definition language: %s"
                uu___6 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___5) in
          FStar_Errors.raise_err uu___4
      | FStar_Syntax_Syntax.Tm_refine uu___ ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_refine is outside of the definition language: %s" uu___3 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___2) in
          FStar_Errors.raise_err uu___1
      | FStar_Syntax_Syntax.Tm_uinst uu___ ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uinst is outside of the definition language: %s" uu___3 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___2) in
          FStar_Errors.raise_err uu___1
      | FStar_Syntax_Syntax.Tm_quoted uu___ ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_quoted is outside of the definition language: %s" uu___3 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___2) in
          FStar_Errors.raise_err uu___1
      | FStar_Syntax_Syntax.Tm_constant uu___ ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_constant is outside of the definition language: %s"
                uu___3 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___2) in
          FStar_Errors.raise_err uu___1
      | FStar_Syntax_Syntax.Tm_match uu___ ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_match is outside of the definition language: %s" uu___3 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___2) in
          FStar_Errors.raise_err uu___1
      | FStar_Syntax_Syntax.Tm_let uu___ ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_let is outside of the definition language: %s" uu___3 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___2) in
          FStar_Errors.raise_err uu___1
      | FStar_Syntax_Syntax.Tm_uvar uu___ ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_uvar is outside of the definition language: %s" uu___3 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___2) in
          FStar_Errors.raise_err uu___1
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Util.format1
                "Tm_unknown is outside of the definition language: %s" uu___2 in
            (FStar_Errors.Fatal_TermOutsideOfDefLanguage, uu___1) in
          FStar_Errors.raise_err uu___
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu___ = FStar_Syntax_Util.unfold_lazy i in
          star_type' env1 uu___
      | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "impossible"
let (is_monadic :
  FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
          (FStar_Util.for_some
             (fun uu___1 ->
                match uu___1 with
                | FStar_Syntax_Syntax.CPS -> true
                | uu___2 -> false))
let rec (is_C : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_app (head, args) when
        FStar_Syntax_Util.is_tuple_constructor head ->
        let r =
          let uu___1 =
            let uu___2 = FStar_List.hd args in
            FStar_Pervasives_Native.fst uu___2 in
          is_C uu___1 in
        if r
        then
          ((let uu___2 =
              let uu___3 =
                FStar_List.for_all
                  (fun uu___4 -> match uu___4 with | (h, uu___5) -> is_C h)
                  args in
              Prims.op_Negation uu___3 in
            if uu___2
            then
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not a C-type (A * C): %s" uu___5 in
                (FStar_Errors.Error_UnexpectedDM4FType, uu___4) in
              FStar_Errors.raise_error uu___3 t.FStar_Syntax_Syntax.pos
            else ());
           true)
        else
          ((let uu___3 =
              let uu___4 =
                FStar_List.for_all
                  (fun uu___5 ->
                     match uu___5 with
                     | (h, uu___6) ->
                         let uu___7 = is_C h in Prims.op_Negation uu___7)
                  args in
              Prims.op_Negation uu___4 in
            if uu___3
            then
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStar_Syntax_Print.term_to_string t in
                  FStar_Util.format1 "Not a C-type (C * A): %s" uu___6 in
                (FStar_Errors.Error_UnexpectedDM4FType, uu___5) in
              FStar_Errors.raise_error uu___4 t.FStar_Syntax_Syntax.pos
            else ());
           false)
    | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
        let uu___1 = nm_of_comp comp in
        (match uu___1 with
         | M t1 ->
             ((let uu___3 = is_C t1 in
               if uu___3
               then
                 let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.format1 "Not a C-type (C -> C): %s" uu___6 in
                   (FStar_Errors.Error_UnexpectedDM4FType, uu___5) in
                 FStar_Errors.raise_error uu___4 t1.FStar_Syntax_Syntax.pos
               else ());
              true)
         | N t1 -> is_C t1)
    | FStar_Syntax_Syntax.Tm_meta (t1, uu___1) -> is_C t1
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu___1) -> is_C t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu___1, uu___2) -> is_C t1
    | uu___1 -> false
let (mk_return :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env1 ->
    fun t ->
      fun e ->
        let mk x = FStar_Syntax_Syntax.mk x e.FStar_Syntax_Syntax.pos in
        let p_type = mk_star_to_type mk env1 t in
        let p =
          FStar_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None p_type in
        let body =
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Syntax_Syntax.bv_to_name p in
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStar_Syntax_Syntax.as_implicit false in
                  (e, uu___5) in
                [uu___4] in
              (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_app uu___1 in
          mk uu___ in
        let uu___ = let uu___1 = FStar_Syntax_Syntax.mk_binder p in [uu___1] in
        FStar_Syntax_Util.abs uu___ body
          (FStar_Pervasives_Native.Some
             (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
let (is_unknown : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Tm_unknown -> true
    | uu___1 -> false
let rec (check :
  env ->
    FStar_Syntax_Syntax.term ->
      nm -> (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      fun context_nm ->
        let return_if uu___ =
          match uu___ with
          | (rec_nm, s_e, u_e) ->
              let check1 t1 t2 =
                let uu___1 =
                  (Prims.op_Negation (is_unknown t2.FStar_Syntax_Syntax.n))
                    &&
                    (let uu___2 =
                       let uu___3 =
                         FStar_TypeChecker_Rel.teq env1.tcenv t1 t2 in
                       FStar_TypeChecker_Env.is_trivial uu___3 in
                     Prims.op_Negation uu___2) in
                if uu___1
                then
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Print.term_to_string e in
                      let uu___5 = FStar_Syntax_Print.term_to_string t1 in
                      let uu___6 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format3
                        "[check]: the expression [%s] has type [%s] but should have type [%s]"
                        uu___4 uu___5 uu___6 in
                    (FStar_Errors.Fatal_TypeMismatch, uu___3) in
                  FStar_Errors.raise_err uu___2
                else () in
              (match (rec_nm, context_nm) with
               | (N t1, N t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (M t1, M t2) -> (check1 t1 t2; (rec_nm, s_e, u_e))
               | (N t1, M t2) ->
                   (check1 t1 t2;
                    (let uu___2 = mk_return env1 t1 s_e in
                     ((M t1), uu___2, u_e)))
               | (M t1, N t2) ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Print.term_to_string e in
                       let uu___4 = FStar_Syntax_Print.term_to_string t1 in
                       let uu___5 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.format3
                         "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                         uu___3 uu___4 uu___5 in
                     (FStar_Errors.Fatal_EffectfulAndPureComputationMismatch,
                       uu___2) in
                   FStar_Errors.raise_err uu___1) in
        let ensure_m env2 e2 =
          let strip_m uu___ =
            match uu___ with
            | (M t, s_e, u_e) -> (t, s_e, u_e)
            | uu___1 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu___ =
                let uu___1 =
                  let uu___2 = FStar_Syntax_Print.term_to_string t in
                  Prims.op_Hat
                    "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                    uu___2 in
                (FStar_Errors.Fatal_LetBoundMonadicMismatch, uu___1) in
              FStar_Errors.raise_error uu___ e2.FStar_Syntax_Syntax.pos
          | M uu___ ->
              let uu___1 = check env2 e2 context_nm in strip_m uu___1 in
        let uu___ =
          let uu___1 = FStar_Syntax_Subst.compress e in
          uu___1.FStar_Syntax_Syntax.n in
        match uu___ with
        | FStar_Syntax_Syntax.Tm_bvar uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStar_Syntax_Syntax.Tm_name uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStar_Syntax_Syntax.Tm_fvar uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStar_Syntax_Syntax.Tm_abs uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStar_Syntax_Syntax.Tm_constant uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStar_Syntax_Syntax.Tm_quoted uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStar_Syntax_Syntax.Tm_app uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu___1 = FStar_Syntax_Util.unfold_lazy i in
            check env1 uu___1 context_nm
        | FStar_Syntax_Syntax.Tm_let ((false, binding::[]), e2) ->
            mk_let env1 binding e2
              (fun env2 -> fun e21 -> check env2 e21 context_nm) ensure_m
        | FStar_Syntax_Syntax.Tm_match (e0, uu___1, branches) ->
            mk_match env1 e0 branches
              (fun env2 -> fun body -> check env2 body context_nm)
        | FStar_Syntax_Syntax.Tm_meta (e1, uu___1) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_uinst (e1, uu___1) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_ascribed (e1, uu___1, uu___2) ->
            check env1 e1 context_nm
        | FStar_Syntax_Syntax.Tm_let uu___1 ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_let %s" uu___3 in
            failwith uu___2
        | FStar_Syntax_Syntax.Tm_type uu___1 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_arrow uu___1 ->
            failwith "impossible (DM stratification)"
        | FStar_Syntax_Syntax.Tm_refine uu___1 ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_refine %s" uu___3 in
            failwith uu___2
        | FStar_Syntax_Syntax.Tm_uvar uu___1 ->
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_uvar %s" uu___3 in
            failwith uu___2
        | FStar_Syntax_Syntax.Tm_delayed uu___1 ->
            failwith "impossible (compressed)"
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu___1 =
              let uu___2 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "[check]: Tm_unknown %s" uu___2 in
            failwith uu___1
and (infer :
  env ->
    FStar_Syntax_Syntax.term ->
      (nm * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mk x = FStar_Syntax_Syntax.mk x e.FStar_Syntax_Syntax.pos in
      let normalize =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Env.Beta;
          FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses] env1.tcenv in
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress e in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStar_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStar_Syntax_Syntax.sort)), e, e)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu___1 = FStar_Syntax_Util.unfold_lazy i in infer env1 uu___1
      | FStar_Syntax_Syntax.Tm_abs (binders, body, rc_opt) ->
          let subst_rc_opt subst rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStar_Syntax_Syntax.residual_effect = uu___1;
                  FStar_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None;
                  FStar_Syntax_Syntax.residual_flags = uu___2;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu___1 =
                  let uu___2 = rc in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_Util.must rc.FStar_Syntax_Syntax.residual_typ in
                      FStar_Syntax_Subst.subst subst uu___5 in
                    FStar_Pervasives_Native.Some uu___4 in
                  {
                    FStar_Syntax_Syntax.residual_effect =
                      (uu___2.FStar_Syntax_Syntax.residual_effect);
                    FStar_Syntax_Syntax.residual_typ = uu___3;
                    FStar_Syntax_Syntax.residual_flags =
                      (uu___2.FStar_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu___1 in
          let binders1 = FStar_Syntax_Subst.open_binders binders in
          let subst = FStar_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStar_Syntax_Subst.subst subst body in
          let rc_opt1 = subst_rc_opt subst rc_opt in
          let env2 =
            let uu___1 = env1 in
            let uu___2 =
              FStar_TypeChecker_Env.push_binders env1.tcenv binders1 in
            {
              tcenv = uu___2;
              subst = (uu___1.subst);
              tc_const = (uu___1.tc_const)
            } in
          let s_binders =
            FStar_List.map
              (fun b ->
                 let sort =
                   star_type' env2
                     (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                 let uu___1 = b in
                 {
                   FStar_Syntax_Syntax.binder_bv =
                     (let uu___2 = b.FStar_Syntax_Syntax.binder_bv in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___2.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___2.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort
                      });
                   FStar_Syntax_Syntax.binder_qual =
                     (uu___1.FStar_Syntax_Syntax.binder_qual);
                   FStar_Syntax_Syntax.binder_attrs =
                     (uu___1.FStar_Syntax_Syntax.binder_attrs)
                 }) binders1 in
          let uu___1 =
            FStar_List.fold_left
              (fun uu___2 ->
                 fun uu___3 ->
                   match (uu___2, uu___3) with
                   | ((env3, acc),
                      { FStar_Syntax_Syntax.binder_bv = bv;
                        FStar_Syntax_Syntax.binder_qual = uu___4;
                        FStar_Syntax_Syntax.binder_attrs = uu___5;_})
                       ->
                       let c = bv.FStar_Syntax_Syntax.sort in
                       let uu___6 = is_C c in
                       if uu___6
                       then
                         let xw =
                           let uu___7 =
                             let uu___8 =
                               FStar_Ident.string_of_id
                                 bv.FStar_Syntax_Syntax.ppname in
                             Prims.op_Hat uu___8 "__w" in
                           let uu___8 = star_type' env3 c in
                           FStar_Syntax_Syntax.gen_bv uu___7
                             FStar_Pervasives_Native.None uu___8 in
                         let x =
                           let uu___7 = bv in
                           let uu___8 =
                             let uu___9 = FStar_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env3 c uu___9 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___7.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___7.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = uu___8
                           } in
                         let env4 =
                           let uu___7 = env3 in
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 =
                                   FStar_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu___11) in
                               FStar_Syntax_Syntax.NT uu___10 in
                             uu___9 :: (env3.subst) in
                           {
                             tcenv = (uu___7.tcenv);
                             subst = uu___8;
                             tc_const = (uu___7.tc_const)
                           } in
                         let uu___7 =
                           let uu___8 = FStar_Syntax_Syntax.mk_binder x in
                           let uu___9 =
                             let uu___10 = FStar_Syntax_Syntax.mk_binder xw in
                             uu___10 :: acc in
                           uu___8 :: uu___9 in
                         (env4, uu___7)
                       else
                         (let x =
                            let uu___8 = bv in
                            let uu___9 =
                              star_type' env3 bv.FStar_Syntax_Syntax.sort in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___8.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___8.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = uu___9
                            } in
                          let uu___8 =
                            let uu___9 = FStar_Syntax_Syntax.mk_binder x in
                            uu___9 :: acc in
                          (env3, uu___8))) (env2, []) binders1 in
          (match uu___1 with
           | (env3, u_binders) ->
               let u_binders1 = FStar_List.rev u_binders in
               let uu___2 =
                 let check_what =
                   let uu___3 = is_monadic rc_opt1 in
                   if uu___3 then check_m else check_n in
                 let uu___3 = check_what env3 body1 in
                 match uu___3 with
                 | (t, s_body, u_body) ->
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = is_monadic rc_opt1 in
                         if uu___6 then M t else N t in
                       comp_of_nm uu___5 in
                     (uu___4, s_body, u_body) in
               (match uu___2 with
                | (comp, s_body, u_body) ->
                    let t = FStar_Syntax_Util.arrow binders1 comp in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStar_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None ->
                               let rc1 =
                                 let uu___3 =
                                   FStar_All.pipe_right
                                     rc.FStar_Syntax_Syntax.residual_flags
                                     (FStar_Util.for_some
                                        (fun uu___4 ->
                                           match uu___4 with
                                           | FStar_Syntax_Syntax.CPS -> true
                                           | uu___5 -> false)) in
                                 if uu___3
                                 then
                                   let uu___4 =
                                     FStar_List.filter
                                       (fun uu___5 ->
                                          match uu___5 with
                                          | FStar_Syntax_Syntax.CPS -> false
                                          | uu___6 -> true)
                                       rc.FStar_Syntax_Syntax.residual_flags in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu___4
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let uu___3 =
                                 FStar_All.pipe_right
                                   rc.FStar_Syntax_Syntax.residual_flags
                                   (FStar_Util.for_some
                                      (fun uu___4 ->
                                         match uu___4 with
                                         | FStar_Syntax_Syntax.CPS -> true
                                         | uu___5 -> false)) in
                               if uu___3
                               then
                                 let flags =
                                   FStar_List.filter
                                     (fun uu___4 ->
                                        match uu___4 with
                                        | FStar_Syntax_Syntax.CPS -> false
                                        | uu___5 -> true)
                                     rc.FStar_Syntax_Syntax.residual_flags in
                                 let uu___4 =
                                   let uu___5 =
                                     let uu___6 = double_star rt in
                                     FStar_Pervasives_Native.Some uu___6 in
                                   FStar_Syntax_Util.mk_residual_comp
                                     FStar_Parser_Const.effect_Tot_lid uu___5
                                     flags in
                                 FStar_Pervasives_Native.Some uu___4
                               else
                                 (let uu___5 =
                                    let uu___6 = rc in
                                    let uu___7 =
                                      let uu___8 = star_type' env3 rt in
                                      FStar_Pervasives_Native.Some uu___8 in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___6.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ =
                                        uu___7;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___6.FStar_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu___5)) in
                    let uu___3 =
                      let comp1 =
                        let uu___4 = is_monadic rc_opt1 in
                        let uu___5 =
                          FStar_Syntax_Subst.subst env3.subst s_body in
                        trans_G env3 (FStar_Syntax_Util.comp_result comp)
                          uu___4 uu___5 in
                      let uu___4 =
                        FStar_Syntax_Util.ascribe u_body
                          ((FStar_Pervasives.Inr comp1),
                            FStar_Pervasives_Native.None) in
                      (uu___4,
                        (FStar_Pervasives_Native.Some
                           (FStar_Syntax_Util.residual_comp_of_comp comp1))) in
                    (match uu___3 with
                     | (u_body1, u_rc_opt) ->
                         let s_body1 =
                           FStar_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStar_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu___7 s_rc_opt in
                               (s_binders1, s_body1, uu___6) in
                             FStar_Syntax_Syntax.Tm_abs uu___5 in
                           mk uu___4 in
                         let u_body2 =
                           FStar_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStar_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   FStar_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu___7 u_rc_opt in
                               (u_binders2, u_body2, uu___6) in
                             FStar_Syntax_Syntax.Tm_abs uu___5 in
                           mk uu___4 in
                         ((N t), s_term, u_term))))
      | FStar_Syntax_Syntax.Tm_fvar
          {
            FStar_Syntax_Syntax.fv_name =
              { FStar_Syntax_Syntax.v = lid;
                FStar_Syntax_Syntax.p = uu___1;_};
            FStar_Syntax_Syntax.fv_delta = uu___2;
            FStar_Syntax_Syntax.fv_qual = uu___3;_}
          ->
          let uu___4 =
            let uu___5 = FStar_TypeChecker_Env.lookup_lid env1.tcenv lid in
            FStar_All.pipe_left FStar_Pervasives_Native.fst uu___5 in
          (match uu___4 with
           | (uu___5, t) ->
               let uu___6 = let uu___7 = normalize t in N uu___7 in
               (uu___6, e, e))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;_},
           a::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu___3 = FStar_Syntax_Util.head_and_args e in
          (match uu___3 with
           | (unary_op, uu___4) ->
               let head = mk (FStar_Syntax_Syntax.Tm_app (unary_op, [a])) in
               let t = mk (FStar_Syntax_Syntax.Tm_app (head, rest1)) in
               infer env1 t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;_},
           a1::a2::hd::rest)
          ->
          let rest1 = hd :: rest in
          let uu___3 = FStar_Syntax_Util.head_and_args e in
          (match uu___3 with
           | (unary_op, uu___4) ->
               let head =
                 mk (FStar_Syntax_Syntax.Tm_app (unary_op, [a1; a2])) in
               let t = mk (FStar_Syntax_Syntax.Tm_app (head, rest1)) in
               infer env1 t)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;_},
           (a, FStar_Pervasives_Native.None)::[])
          ->
          let uu___3 = infer env1 a in
          (match uu___3 with
           | (t, s, u) ->
               let uu___4 = FStar_Syntax_Util.head_and_args e in
               (match uu___4 with
                | (head, uu___5) ->
                    let uu___6 =
                      let uu___7 =
                        FStar_Syntax_Syntax.tabbrev
                          FStar_Parser_Const.range_lid in
                      N uu___7 in
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          let uu___10 =
                            let uu___11 = FStar_Syntax_Syntax.as_arg s in
                            [uu___11] in
                          (head, uu___10) in
                        FStar_Syntax_Syntax.Tm_app uu___9 in
                      mk uu___8 in
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            let uu___12 = FStar_Syntax_Syntax.as_arg u in
                            [uu___12] in
                          (head, uu___11) in
                        FStar_Syntax_Syntax.Tm_app uu___10 in
                      mk uu___9 in
                    (uu___6, uu___7, uu___8)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;_},
           (a1, uu___3)::a2::[])
          ->
          let uu___4 = infer env1 a1 in
          (match uu___4 with
           | (t, s, u) ->
               let uu___5 = FStar_Syntax_Util.head_and_args e in
               (match uu___5 with
                | (head, uu___6) ->
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          let uu___10 =
                            let uu___11 = FStar_Syntax_Syntax.as_arg s in
                            [uu___11; a2] in
                          (head, uu___10) in
                        FStar_Syntax_Syntax.Tm_app uu___9 in
                      mk uu___8 in
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            let uu___12 = FStar_Syntax_Syntax.as_arg u in
                            [uu___12; a2] in
                          (head, uu___11) in
                        FStar_Syntax_Syntax.Tm_app uu___10 in
                      mk uu___9 in
                    (t, uu___7, uu___8)))
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of);
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;_},
           uu___3)
          ->
          let uu___4 =
            let uu___5 =
              let uu___6 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu___6 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu___5) in
          FStar_Errors.raise_error uu___4 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of);
             FStar_Syntax_Syntax.pos = uu___1;
             FStar_Syntax_Syntax.vars = uu___2;_},
           uu___3)
          ->
          let uu___4 =
            let uu___5 =
              let uu___6 = FStar_Syntax_Print.term_to_string e in
              FStar_Util.format1 "DMFF: Ill-applied constant %s" uu___6 in
            (FStar_Errors.Fatal_IllAppliedConstant, uu___5) in
          FStar_Errors.raise_error uu___4 e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head, args) ->
          let uu___1 = check_n env1 head in
          (match uu___1 with
           | (t_head, s_head, u_head) ->
               let is_arrow t =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Subst.compress t in
                   uu___3.FStar_Syntax_Syntax.n in
                 match uu___2 with
                 | FStar_Syntax_Syntax.Tm_arrow uu___3 -> true
                 | uu___3 -> false in
               let rec flatten t =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Subst.compress t in
                   uu___3.FStar_Syntax_Syntax.n in
                 match uu___2 with
                 | FStar_Syntax_Syntax.Tm_arrow
                     (binders,
                      {
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                          (t1, uu___3);
                        FStar_Syntax_Syntax.pos = uu___4;
                        FStar_Syntax_Syntax.vars = uu___5;_})
                     when is_arrow t1 ->
                     let uu___6 = flatten t1 in
                     (match uu___6 with
                      | (binders', comp) ->
                          ((FStar_List.append binders binders'), comp))
                 | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
                     (binders, comp)
                 | FStar_Syntax_Syntax.Tm_ascribed (e1, uu___3, uu___4) ->
                     flatten e1
                 | uu___3 ->
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           FStar_Syntax_Print.term_to_string t_head in
                         FStar_Util.format1 "%s: not a function type" uu___6 in
                       (FStar_Errors.Fatal_NotFunctionType, uu___5) in
                     FStar_Errors.raise_err uu___4 in
               let uu___2 = flatten t_head in
               (match uu___2 with
                | (binders, comp) ->
                    let n = FStar_List.length binders in
                    let n' = FStar_List.length args in
                    (if
                       (FStar_List.length binders) < (FStar_List.length args)
                     then
                       (let uu___4 =
                          let uu___5 =
                            let uu___6 = FStar_Util.string_of_int n in
                            let uu___7 = FStar_Util.string_of_int (n' - n) in
                            let uu___8 = FStar_Util.string_of_int n in
                            FStar_Util.format3
                              "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                              uu___6 uu___7 uu___8 in
                          (FStar_Errors.Fatal_BinderAndArgsLengthMismatch,
                            uu___5) in
                        FStar_Errors.raise_err uu___4)
                     else ();
                     (let uu___4 = FStar_Syntax_Subst.open_comp binders comp in
                      match uu___4 with
                      | (binders1, comp1) ->
                          let rec final_type subst uu___5 args1 =
                            match uu___5 with
                            | (binders2, comp2) ->
                                (match (binders2, args1) with
                                 | ([], []) ->
                                     let uu___6 =
                                       FStar_Syntax_Subst.subst_comp subst
                                         comp2 in
                                     nm_of_comp uu___6
                                 | (binders3, []) ->
                                     let uu___6 =
                                       let uu___7 =
                                         let uu___8 =
                                           let uu___9 =
                                             mk
                                               (FStar_Syntax_Syntax.Tm_arrow
                                                  (binders3, comp2)) in
                                           FStar_Syntax_Subst.subst subst
                                             uu___9 in
                                         FStar_Syntax_Subst.compress uu___8 in
                                       uu___7.FStar_Syntax_Syntax.n in
                                     (match uu___6 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (binders4, comp3) ->
                                          let uu___7 =
                                            let uu___8 =
                                              let uu___9 =
                                                let uu___10 =
                                                  FStar_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                (binders4, uu___10) in
                                              FStar_Syntax_Syntax.Tm_arrow
                                                uu___9 in
                                            mk uu___8 in
                                          N uu___7
                                      | uu___7 -> failwith "wat?")
                                 | ([], uu___6::uu___7) ->
                                     failwith "just checked that?!"
                                 | ({ FStar_Syntax_Syntax.binder_bv = bv;
                                      FStar_Syntax_Syntax.binder_qual =
                                        uu___6;
                                      FStar_Syntax_Syntax.binder_attrs =
                                        uu___7;_}::binders3,
                                    (arg, uu___8)::args2) ->
                                     final_type
                                       ((FStar_Syntax_Syntax.NT (bv, arg)) ::
                                       subst) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu___5 = FStar_List.splitAt n' binders1 in
                          (match uu___5 with
                           | (binders2, uu___6) ->
                               let uu___7 =
                                 let uu___8 =
                                   FStar_List.map2
                                     (fun uu___9 ->
                                        fun uu___10 ->
                                          match (uu___9, uu___10) with
                                          | ({
                                               FStar_Syntax_Syntax.binder_bv
                                                 = bv;
                                               FStar_Syntax_Syntax.binder_qual
                                                 = uu___11;
                                               FStar_Syntax_Syntax.binder_attrs
                                                 = uu___12;_},
                                             (arg, q)) ->
                                              let uu___13 =
                                                let uu___14 =
                                                  FStar_Syntax_Subst.compress
                                                    bv.FStar_Syntax_Syntax.sort in
                                                uu___14.FStar_Syntax_Syntax.n in
                                              (match uu___13 with
                                               | FStar_Syntax_Syntax.Tm_type
                                                   uu___14 ->
                                                   let uu___15 =
                                                     let uu___16 =
                                                       star_type' env1 arg in
                                                     (uu___16, q) in
                                                   (uu___15, [(arg, q)])
                                               | uu___14 ->
                                                   let uu___15 =
                                                     check_n env1 arg in
                                                   (match uu___15 with
                                                    | (uu___16, s_arg, u_arg)
                                                        ->
                                                        let uu___17 =
                                                          let uu___18 =
                                                            is_C
                                                              bv.FStar_Syntax_Syntax.sort in
                                                          if uu___18
                                                          then
                                                            let uu___19 =
                                                              let uu___20 =
                                                                FStar_Syntax_Subst.subst
                                                                  env1.subst
                                                                  s_arg in
                                                              (uu___20, q) in
                                                            [uu___19;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q), uu___17))))
                                     binders2 args in
                                 FStar_List.split uu___8 in
                               (match uu___7 with
                                | (s_args, u_args) ->
                                    let u_args1 = FStar_List.flatten u_args in
                                    let uu___8 =
                                      mk
                                        (FStar_Syntax_Syntax.Tm_app
                                           (s_head, s_args)) in
                                    let uu___9 =
                                      mk
                                        (FStar_Syntax_Syntax.Tm_app
                                           (u_head, u_args1)) in
                                    (final_type1, uu___8, uu___9)))))))
      | FStar_Syntax_Syntax.Tm_let ((false, binding::[]), e2) ->
          mk_let env1 binding e2 infer check_m
      | FStar_Syntax_Syntax.Tm_match (e0, uu___1, branches) ->
          mk_match env1 e0 branches infer
      | FStar_Syntax_Syntax.Tm_uinst (e1, uu___1) -> infer env1 e1
      | FStar_Syntax_Syntax.Tm_meta (e1, uu___1) -> infer env1 e1
      | FStar_Syntax_Syntax.Tm_ascribed (e1, uu___1, uu___2) -> infer env1 e1
      | FStar_Syntax_Syntax.Tm_constant c ->
          let uu___1 = let uu___2 = env1.tc_const c in N uu___2 in
          (uu___1, e, e)
      | FStar_Syntax_Syntax.Tm_quoted (tm, qt) ->
          ((N FStar_Syntax_Syntax.t_term), e, e)
      | FStar_Syntax_Syntax.Tm_let uu___1 ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_let %s" uu___3 in
          failwith uu___2
      | FStar_Syntax_Syntax.Tm_type uu___1 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_arrow uu___1 ->
          failwith "impossible (DM stratification)"
      | FStar_Syntax_Syntax.Tm_refine uu___1 ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_refine %s" uu___3 in
          failwith uu___2
      | FStar_Syntax_Syntax.Tm_uvar uu___1 ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_uvar %s" uu___3 in
          failwith uu___2
      | FStar_Syntax_Syntax.Tm_delayed uu___1 ->
          failwith "impossible (compressed)"
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "[infer]: Tm_unknown %s" uu___2 in
          failwith uu___1
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
  fun env1 ->
    fun e0 ->
      fun branches ->
        fun f ->
          let mk x = FStar_Syntax_Syntax.mk x e0.FStar_Syntax_Syntax.pos in
          let uu___ = check_n env1 e0 in
          match uu___ with
          | (uu___1, s_e0, u_e0) ->
              let uu___2 =
                let uu___3 =
                  FStar_List.map
                    (fun b ->
                       let uu___4 = FStar_Syntax_Subst.open_branch b in
                       match uu___4 with
                       | (pat, FStar_Pervasives_Native.None, body) ->
                           let env2 =
                             let uu___5 = env1 in
                             let uu___6 =
                               let uu___7 = FStar_Syntax_Syntax.pat_bvs pat in
                               FStar_List.fold_left
                                 FStar_TypeChecker_Env.push_bv env1.tcenv
                                 uu___7 in
                             {
                               tcenv = uu___6;
                               subst = (uu___5.subst);
                               tc_const = (uu___5.tc_const)
                             } in
                           let uu___5 = f env2 body in
                           (match uu___5 with
                            | (nm1, s_body, u_body) ->
                                (nm1,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu___5 ->
                           FStar_Errors.raise_err
                             (FStar_Errors.Fatal_WhenClauseNotSupported,
                               "No when clauses in the definition language"))
                    branches in
                FStar_List.split uu___3 in
              (match uu___2 with
               | (nms, branches1) ->
                   let t1 =
                     let uu___3 = FStar_List.hd nms in
                     match uu___3 with | M t11 -> t11 | N t11 -> t11 in
                   let has_m =
                     FStar_List.existsb
                       (fun uu___3 ->
                          match uu___3 with
                          | M uu___4 -> true
                          | uu___4 -> false) nms in
                   let uu___3 =
                     let uu___4 =
                       FStar_List.map2
                         (fun nm1 ->
                            fun uu___5 ->
                              match uu___5 with
                              | (pat, guard, (s_body, u_body, original_body))
                                  ->
                                  (match (nm1, has_m) with
                                   | (N t2, false) ->
                                       (nm1, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (M t2, true) ->
                                       (nm1, (pat, guard, s_body),
                                         (pat, guard, u_body))
                                   | (N t2, true) ->
                                       let uu___6 =
                                         check env1 original_body (M t2) in
                                       (match uu___6 with
                                        | (uu___7, s_body1, u_body1) ->
                                            ((M t2), (pat, guard, s_body1),
                                              (pat, guard, u_body1)))
                                   | (M uu___6, false) ->
                                       failwith "impossible")) nms branches1 in
                     FStar_List.unzip3 uu___4 in
                   (match uu___3 with
                    | (nms1, s_branches, u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk env1 t1 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStar_List.map
                              (fun uu___4 ->
                                 match uu___4 with
                                 | (pat, guard, s_body) ->
                                     let s_body1 =
                                       let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             let uu___8 =
                                               let uu___9 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu___10 =
                                                 FStar_Syntax_Syntax.as_implicit
                                                   false in
                                               (uu___9, uu___10) in
                                             [uu___8] in
                                           (s_body, uu___7) in
                                         FStar_Syntax_Syntax.Tm_app uu___6 in
                                       mk uu___5 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              s_branches1 in
                          let u_branches1 =
                            FStar_List.map FStar_Syntax_Subst.close_branch
                              u_branches in
                          let s_e =
                            let uu___4 =
                              let uu___5 = FStar_Syntax_Syntax.mk_binder p in
                              [uu___5] in
                            let uu___5 =
                              mk
                                (FStar_Syntax_Syntax.Tm_match
                                   (s_e0, FStar_Pervasives_Native.None,
                                     s_branches2)) in
                            FStar_Syntax_Util.abs uu___4 uu___5
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.mk_binder uu___6 in
                              [uu___5] in
                            let uu___5 =
                              FStar_Syntax_Syntax.mk_Total
                                FStar_Syntax_Util.ktype0 in
                            FStar_Syntax_Util.arrow uu___4 uu___5 in
                          let uu___4 =
                            mk
                              (FStar_Syntax_Syntax.Tm_ascribed
                                 (s_e,
                                   ((FStar_Pervasives.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None)) in
                          let uu___5 =
                            mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (u_e0, FStar_Pervasives_Native.None,
                                   u_branches1)) in
                          ((M t1), uu___4, uu___5)
                        else
                          (let s_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               s_branches in
                           let u_branches1 =
                             FStar_List.map FStar_Syntax_Subst.close_branch
                               u_branches in
                           let t1_star = t1 in
                           let uu___5 =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (s_e0, FStar_Pervasives_Native.None,
                                          s_branches1)) in
                                 (uu___8,
                                   ((FStar_Pervasives.Inl t1_star),
                                     FStar_Pervasives_Native.None),
                                   FStar_Pervasives_Native.None) in
                               FStar_Syntax_Syntax.Tm_ascribed uu___7 in
                             mk uu___6 in
                           let uu___6 =
                             mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (u_e0, FStar_Pervasives_Native.None,
                                    u_branches1)) in
                           ((N t1), uu___5, uu___6))))
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
  fun env1 ->
    fun binding ->
      fun e2 ->
        fun proceed ->
          fun ensure_m ->
            let mk x = FStar_Syntax_Syntax.mk x e2.FStar_Syntax_Syntax.pos in
            let e1 = binding.FStar_Syntax_Syntax.lbdef in
            let x = FStar_Util.left binding.FStar_Syntax_Syntax.lbname in
            let x_binders =
              let uu___ = FStar_Syntax_Syntax.mk_binder x in [uu___] in
            let uu___ = FStar_Syntax_Subst.open_term x_binders e2 in
            match uu___ with
            | (x_binders1, e21) ->
                let uu___1 = infer env1 e1 in
                (match uu___1 with
                 | (N t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu___2 = is_C t1 in
                       if uu___2
                       then
                         let uu___3 = binding in
                         let uu___4 =
                           let uu___5 =
                             FStar_Syntax_Subst.subst env1.subst s_e1 in
                           trans_F_ env1 t1 uu___5 in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___3.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs =
                             (uu___3.FStar_Syntax_Syntax.lbunivs);
                           FStar_Syntax_Syntax.lbtyp = uu___4;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___3.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef =
                             (uu___3.FStar_Syntax_Syntax.lbdef);
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___3.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___3.FStar_Syntax_Syntax.lbpos)
                         }
                       else binding in
                     let env2 =
                       let uu___2 = env1 in
                       let uu___3 =
                         FStar_TypeChecker_Env.push_bv env1.tcenv
                           (let uu___4 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___4.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___4.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         tcenv = uu___3;
                         subst = (uu___2.subst);
                         tc_const = (uu___2.tc_const)
                       } in
                     let uu___2 = proceed env2 e21 in
                     (match uu___2 with
                      | (nm_rec, s_e2, u_e2) ->
                          let s_binding =
                            let uu___3 = binding in
                            let uu___4 =
                              star_type' env2
                                binding.FStar_Syntax_Syntax.lbtyp in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (uu___3.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (uu___3.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp = uu___4;
                              FStar_Syntax_Syntax.lbeff =
                                (uu___3.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef =
                                (uu___3.FStar_Syntax_Syntax.lbdef);
                              FStar_Syntax_Syntax.lbattrs =
                                (uu___3.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (uu___3.FStar_Syntax_Syntax.lbpos)
                            } in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  FStar_Syntax_Subst.close x_binders1 s_e2 in
                                ((false,
                                   [(let uu___7 = s_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___7.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___7.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___7.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___7.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = s_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___7.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___7.FStar_Syntax_Syntax.lbpos)
                                     })]), uu___6) in
                              FStar_Syntax_Syntax.Tm_let uu___5 in
                            mk uu___4 in
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___8 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___8.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___8.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___8.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___8.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___8.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___8.FStar_Syntax_Syntax.lbpos)
                                     })]), uu___7) in
                              FStar_Syntax_Syntax.Tm_let uu___6 in
                            mk uu___5 in
                          (nm_rec, uu___3, uu___4))
                 | (M t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu___2 = binding in
                       {
                         FStar_Syntax_Syntax.lbname =
                           (uu___2.FStar_Syntax_Syntax.lbname);
                         FStar_Syntax_Syntax.lbunivs =
                           (uu___2.FStar_Syntax_Syntax.lbunivs);
                         FStar_Syntax_Syntax.lbtyp = t1;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_PURE_lid;
                         FStar_Syntax_Syntax.lbdef =
                           (uu___2.FStar_Syntax_Syntax.lbdef);
                         FStar_Syntax_Syntax.lbattrs =
                           (uu___2.FStar_Syntax_Syntax.lbattrs);
                         FStar_Syntax_Syntax.lbpos =
                           (uu___2.FStar_Syntax_Syntax.lbpos)
                       } in
                     let env2 =
                       let uu___2 = env1 in
                       let uu___3 =
                         FStar_TypeChecker_Env.push_bv env1.tcenv
                           (let uu___4 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___4.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___4.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }) in
                       {
                         tcenv = uu___3;
                         subst = (uu___2.subst);
                         tc_const = (uu___2.tc_const)
                       } in
                     let uu___2 = ensure_m env2 e21 in
                     (match uu___2 with
                      | (t2, s_e2, u_e2) ->
                          let p_type = mk_star_to_type mk env2 t2 in
                          let p =
                            FStar_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 =
                                      FStar_Syntax_Syntax.bv_to_name p in
                                    let uu___8 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu___7, uu___8) in
                                  [uu___6] in
                                (s_e2, uu___5) in
                              FStar_Syntax_Syntax.Tm_app uu___4 in
                            mk uu___3 in
                          let s_e22 =
                            FStar_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let body =
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (s_e22, uu___7) in
                                  [uu___6] in
                                (s_e1, uu___5) in
                              FStar_Syntax_Syntax.Tm_app uu___4 in
                            mk uu___3 in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 = FStar_Syntax_Syntax.mk_binder p in
                              [uu___5] in
                            FStar_Syntax_Util.abs uu___4 body
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_tot
                                    FStar_Syntax_Util.ktype0)) in
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Subst.close x_binders1 u_e2 in
                                ((false,
                                   [(let uu___8 = u_binding in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (uu___8.FStar_Syntax_Syntax.lbname);
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___8.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___8.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___8.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef = u_e1;
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___8.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___8.FStar_Syntax_Syntax.lbpos)
                                     })]), uu___7) in
                              FStar_Syntax_Syntax.Tm_let uu___6 in
                            mk uu___5 in
                          ((M t2), uu___3, uu___4)))
and (check_n :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mn =
        let uu___ =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            e.FStar_Syntax_Syntax.pos in
        N uu___ in
      let uu___ = check env1 e mn in
      match uu___ with
      | (N t, s_e, u_e) -> (t, s_e, u_e)
      | uu___1 -> failwith "[check_n]: impossible"
and (check_m :
  env_ ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mn =
        let uu___ =
          FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
            e.FStar_Syntax_Syntax.pos in
        M uu___ in
      let uu___ = check env1 e mn in
      match uu___ with
      | (M t, s_e, u_e) -> (t, s_e, u_e)
      | uu___1 -> failwith "[check_m]: impossible"
and (comp_of_nm : nm_ -> FStar_Syntax_Syntax.comp) =
  fun nm1 ->
    match nm1 with | N t -> FStar_Syntax_Syntax.mk_Total t | M t -> mk_M t
and (mk_M : FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp) =
  fun t ->
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
  = fun t -> FStar_Syntax_Util.comp_result t
and (trans_F_ :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun wp ->
        (let uu___1 = let uu___2 = is_C c in Prims.op_Negation uu___2 in
         if uu___1
         then
           let uu___2 =
             let uu___3 =
               let uu___4 = FStar_Syntax_Print.term_to_string c in
               FStar_Util.format1 "Not a DM4F C-type: %s" uu___4 in
             (FStar_Errors.Error_UnexpectedDM4FType, uu___3) in
           FStar_Errors.raise_error uu___2 c.FStar_Syntax_Syntax.pos
         else ());
        (let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos in
         let uu___1 =
           let uu___2 = FStar_Syntax_Subst.compress c in
           uu___2.FStar_Syntax_Syntax.n in
         match uu___1 with
         | FStar_Syntax_Syntax.Tm_app (head, args) ->
             let uu___2 = FStar_Syntax_Util.head_and_args wp in
             (match uu___2 with
              | (wp_head, wp_args) ->
                  ((let uu___4 =
                      (Prims.op_Negation
                         ((FStar_List.length wp_args) =
                            (FStar_List.length args)))
                        ||
                        (let uu___5 =
                           let uu___6 =
                             FStar_Parser_Const.mk_tuple_data_lid
                               (FStar_List.length wp_args)
                               FStar_Range.dummyRange in
                           FStar_Syntax_Util.is_constructor wp_head uu___6 in
                         Prims.op_Negation uu___5) in
                    if uu___4 then failwith "mismatch" else ());
                   (let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          FStar_List.map2
                            (fun uu___7 ->
                               fun uu___8 ->
                                 match (uu___7, uu___8) with
                                 | ((arg, q), (wp_arg, q')) ->
                                     let print_implicit q1 =
                                       let uu___9 =
                                         FStar_Syntax_Syntax.is_implicit q1 in
                                       if uu___9
                                       then "implicit"
                                       else "explicit" in
                                     ((let uu___10 =
                                         let uu___11 =
                                           FStar_Syntax_Util.eq_aqual q q' in
                                         uu___11 <> FStar_Syntax_Util.Equal in
                                       if uu___10
                                       then
                                         let uu___11 =
                                           let uu___12 =
                                             let uu___13 = print_implicit q in
                                             let uu___14 = print_implicit q' in
                                             FStar_Util.format2
                                               "Incoherent implicit qualifiers %s %s\n"
                                               uu___13 uu___14 in
                                           (FStar_Errors.Warning_IncoherentImplicitQualifier,
                                             uu___12) in
                                         FStar_Errors.log_issue
                                           head.FStar_Syntax_Syntax.pos
                                           uu___11
                                       else ());
                                      (let uu___10 = trans_F_ env1 arg wp_arg in
                                       (uu___10, q)))) args wp_args in
                        (head, uu___6) in
                      FStar_Syntax_Syntax.Tm_app uu___5 in
                    mk uu___4)))
         | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
             let binders1 = FStar_Syntax_Util.name_binders binders in
             let uu___2 = FStar_Syntax_Subst.open_comp binders1 comp in
             (match uu___2 with
              | (binders_orig, comp1) ->
                  let uu___3 =
                    let uu___4 =
                      FStar_List.map
                        (fun b ->
                           let uu___5 =
                             ((b.FStar_Syntax_Syntax.binder_bv),
                               (b.FStar_Syntax_Syntax.binder_qual)) in
                           match uu___5 with
                           | (bv, q) ->
                               let h = bv.FStar_Syntax_Syntax.sort in
                               let uu___6 = is_C h in
                               if uu___6
                               then
                                 let w' =
                                   let uu___7 =
                                     let uu___8 =
                                       FStar_Ident.string_of_id
                                         bv.FStar_Syntax_Syntax.ppname in
                                     Prims.op_Hat uu___8 "__w'" in
                                   let uu___8 = star_type' env1 h in
                                   FStar_Syntax_Syntax.gen_bv uu___7
                                     FStar_Pervasives_Native.None uu___8 in
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       let uu___10 = b in
                                       let uu___11 =
                                         let uu___12 =
                                           let uu___13 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env1 h uu___13 in
                                         FStar_Syntax_Syntax.null_bv uu___12 in
                                       {
                                         FStar_Syntax_Syntax.binder_bv =
                                           uu___11;
                                         FStar_Syntax_Syntax.binder_qual =
                                           (uu___10.FStar_Syntax_Syntax.binder_qual);
                                         FStar_Syntax_Syntax.binder_attrs =
                                           (uu___10.FStar_Syntax_Syntax.binder_attrs)
                                       } in
                                     [uu___9] in
                                   (let uu___9 = b in
                                    {
                                      FStar_Syntax_Syntax.binder_bv = w';
                                      FStar_Syntax_Syntax.binder_qual =
                                        (uu___9.FStar_Syntax_Syntax.binder_qual);
                                      FStar_Syntax_Syntax.binder_attrs =
                                        (uu___9.FStar_Syntax_Syntax.binder_attrs)
                                    }) :: uu___8 in
                                 (w', uu___7)
                               else
                                 (let x =
                                    let uu___8 =
                                      let uu___9 =
                                        FStar_Ident.string_of_id
                                          bv.FStar_Syntax_Syntax.ppname in
                                      Prims.op_Hat uu___9 "__x" in
                                    let uu___9 = star_type' env1 h in
                                    FStar_Syntax_Syntax.gen_bv uu___8
                                      FStar_Pervasives_Native.None uu___9 in
                                  (x,
                                    [(let uu___8 = b in
                                      {
                                        FStar_Syntax_Syntax.binder_bv = x;
                                        FStar_Syntax_Syntax.binder_qual =
                                          (uu___8.FStar_Syntax_Syntax.binder_qual);
                                        FStar_Syntax_Syntax.binder_attrs =
                                          (uu___8.FStar_Syntax_Syntax.binder_attrs)
                                      })]))) binders_orig in
                    FStar_List.split uu___4 in
                  (match uu___3 with
                   | (bvs, binders2) ->
                       let binders3 = FStar_List.flatten binders2 in
                       let comp2 =
                         let uu___4 =
                           let uu___5 =
                             FStar_Syntax_Syntax.binders_of_list bvs in
                           FStar_Syntax_Util.rename_binders binders_orig
                             uu___5 in
                         FStar_Syntax_Subst.subst_comp uu___4 comp1 in
                       let app =
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               FStar_List.map
                                 (fun bv ->
                                    let uu___7 =
                                      FStar_Syntax_Syntax.bv_to_name bv in
                                    let uu___8 =
                                      FStar_Syntax_Syntax.as_implicit false in
                                    (uu___7, uu___8)) bvs in
                             (wp, uu___6) in
                           FStar_Syntax_Syntax.Tm_app uu___5 in
                         mk uu___4 in
                       let comp3 =
                         let uu___4 = type_of_comp comp2 in
                         let uu___5 = is_monadic_comp comp2 in
                         trans_G env1 uu___4 uu___5 app in
                       FStar_Syntax_Util.arrow binders3 comp3))
         | FStar_Syntax_Syntax.Tm_ascribed (e, uu___2, uu___3) ->
             trans_F_ env1 e wp
         | uu___2 -> failwith "impossible trans_F_")
and (trans_G :
  env_ ->
    FStar_Syntax_Syntax.typ ->
      Prims.bool -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.comp)
  =
  fun env1 ->
    fun h ->
      fun is_monadic1 ->
        fun wp ->
          if is_monadic1
          then
            let uu___ =
              let uu___1 = star_type' env1 h in
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Syntax.as_implicit false in
                  (wp, uu___4) in
                [uu___3] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  [FStar_Syntax_Syntax.U_unknown];
                FStar_Syntax_Syntax.effect_name =
                  FStar_Parser_Const.effect_PURE_lid;
                FStar_Syntax_Syntax.result_typ = uu___1;
                FStar_Syntax_Syntax.effect_args = uu___2;
                FStar_Syntax_Syntax.flags = []
              } in
            FStar_Syntax_Syntax.mk_Comp uu___
          else
            (let uu___1 = trans_F_ env1 h wp in
             FStar_Syntax_Syntax.mk_Total uu___1)
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
  fun env1 -> fun t -> let uu___ = n env1.tcenv t in star_type' env1 uu___
let (star_expr :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term *
        FStar_Syntax_Syntax.term))
  = fun env1 -> fun t -> let uu___ = n env1.tcenv t in check_n env1 uu___
let (trans_F :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun wp ->
        let uu___ = n env1.tcenv c in
        let uu___1 = n env1.tcenv wp in trans_F_ env1 uu___ uu___1
let (recheck_debug :
  Prims.string ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun env1 ->
      fun t ->
        (let uu___1 =
           FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED") in
         if uu___1
         then
           let uu___2 = FStar_Syntax_Print.term_to_string t in
           FStar_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu___2
         else ());
        (let uu___1 = FStar_TypeChecker_TcTerm.tc_term env1 t in
         match uu___1 with
         | (t', uu___2, uu___3) ->
             ((let uu___5 =
                 FStar_TypeChecker_Env.debug env1 (FStar_Options.Other "ED") in
               if uu___5
               then
                 let uu___6 = FStar_Syntax_Print.term_to_string t' in
                 FStar_Util.print1 "Re-checked; got:\n%s\n----------\n"
                   uu___6
               else ());
              t'))
let (cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env1 ->
    fun ed ->
      let uu___ =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature) in
      match uu___ with
      | (effect_binders_un, signature_un) ->
          let uu___1 =
            FStar_TypeChecker_TcTerm.tc_tparams env1 effect_binders_un in
          (match uu___1 with
           | (effect_binders, env2, uu___2) ->
               let uu___3 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env2 signature_un in
               (match uu___3 with
                | (signature, uu___4) ->
                    let raise_error uu___5 =
                      match uu___5 with
                      | (e, err_msg) ->
                          FStar_Errors.raise_error (e, err_msg)
                            signature.FStar_Syntax_Syntax.pos in
                    let effect_binders1 =
                      FStar_List.map
                        (fun b ->
                           let uu___5 = b in
                           let uu___6 =
                             let uu___7 = b.FStar_Syntax_Syntax.binder_bv in
                             let uu___8 =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.EraseUniverses] env2
                                 (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___7.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___7.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu___8
                             } in
                           {
                             FStar_Syntax_Syntax.binder_bv = uu___6;
                             FStar_Syntax_Syntax.binder_qual =
                               (uu___5.FStar_Syntax_Syntax.binder_qual);
                             FStar_Syntax_Syntax.binder_attrs =
                               (uu___5.FStar_Syntax_Syntax.binder_attrs)
                           }) effect_binders in
                    let uu___5 =
                      let uu___6 =
                        let uu___7 = FStar_Syntax_Subst.compress signature_un in
                        uu___7.FStar_Syntax_Syntax.n in
                      match uu___6 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ({ FStar_Syntax_Syntax.binder_bv = a;
                             FStar_Syntax_Syntax.binder_qual = uu___7;
                             FStar_Syntax_Syntax.binder_attrs = uu___8;_}::[],
                           effect_marker)
                          -> (a, effect_marker)
                      | uu___7 ->
                          raise_error
                            (FStar_Errors.Fatal_BadSignatureShape,
                              "bad shape for effect-for-free signature") in
                    (match uu___5 with
                     | (a, effect_marker) ->
                         let a1 =
                           let uu___6 = FStar_Syntax_Syntax.is_null_bv a in
                           if uu___6
                           then
                             let uu___7 =
                               let uu___8 = FStar_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu___8 in
                             FStar_Syntax_Syntax.gen_bv "a" uu___7
                               a.FStar_Syntax_Syntax.sort
                           else a in
                         let open_and_check env3 other_binders t =
                           let subst =
                             FStar_Syntax_Subst.opening_of_binders
                               (FStar_List.append effect_binders1
                                  other_binders) in
                           let t1 = FStar_Syntax_Subst.subst subst t in
                           let uu___6 =
                             FStar_TypeChecker_TcTerm.tc_term env3 t1 in
                           match uu___6 with
                           | (t2, comp, uu___7) -> (t2, comp) in
                         let mk x =
                           FStar_Syntax_Syntax.mk x
                             signature.FStar_Syntax_Syntax.pos in
                         let uu___6 =
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu___9 FStar_Util.must in
                             FStar_All.pipe_right uu___8
                               FStar_Pervasives_Native.snd in
                           open_and_check env2 [] uu___7 in
                         (match uu___6 with
                          | (repr, _comp) ->
                              ((let uu___8 =
                                  FStar_TypeChecker_Env.debug env2
                                    (FStar_Options.Other "ED") in
                                if uu___8
                                then
                                  let uu___9 =
                                    FStar_Syntax_Print.term_to_string repr in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu___9
                                else ());
                               (let ed_range =
                                  FStar_TypeChecker_Env.get_range env2 in
                                let dmff_env =
                                  empty env2
                                    (FStar_TypeChecker_TcTerm.tc_constant
                                       env2 FStar_Range.dummyRange) in
                                let wp_type = star_type dmff_env repr in
                                let uu___8 = recheck_debug "*" env2 wp_type in
                                let wp_a =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu___15 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false in
                                            (uu___14, uu___15) in
                                          [uu___13] in
                                        (wp_type, uu___12) in
                                      FStar_Syntax_Syntax.Tm_app uu___11 in
                                    mk uu___10 in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta] env2 uu___9 in
                                let effect_signature =
                                  let binders =
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_Syntax_Syntax.as_implicit false in
                                      FStar_Syntax_Syntax.mk_binder_with_attrs
                                        a1 uu___10 [] in
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStar_All.pipe_right uu___12
                                          FStar_Syntax_Syntax.mk_binder in
                                      [uu___11] in
                                    uu___9 :: uu___10 in
                                  let binders1 =
                                    FStar_Syntax_Subst.close_binders binders in
                                  mk
                                    (FStar_Syntax_Syntax.Tm_arrow
                                       (binders1, effect_marker)) in
                                let uu___9 =
                                  recheck_debug
                                    "turned into the effect signature" env2
                                    effect_signature in
                                let sigelts = FStar_Util.mk_ref [] in
                                let mk_lid name =
                                  FStar_Syntax_Util.dm4f_lid ed name in
                                let elaborate_and_star dmff_env1
                                  other_binders item =
                                  let env3 = get_env dmff_env1 in
                                  let uu___10 = item in
                                  match uu___10 with
                                  | (u_item, item1) ->
                                      let uu___11 =
                                        open_and_check env3 other_binders
                                          item1 in
                                      (match uu___11 with
                                       | (item2, item_comp) ->
                                           ((let uu___13 =
                                               let uu___14 =
                                                 FStar_TypeChecker_Common.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu___14 in
                                             if uu___13
                                             then
                                               let uu___14 =
                                                 let uu___15 =
                                                   let uu___16 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2 in
                                                   let uu___17 =
                                                     FStar_TypeChecker_Common.lcomp_to_string
                                                       item_comp in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu___16 uu___17 in
                                                 (FStar_Errors.Fatal_ComputationNotTotal,
                                                   uu___15) in
                                               FStar_Errors.raise_err uu___14
                                             else ());
                                            (let uu___13 =
                                               star_expr dmff_env1 item2 in
                                             match uu___13 with
                                             | (item_t, item_wp, item_elab)
                                                 ->
                                                 let uu___14 =
                                                   recheck_debug "*" env3
                                                     item_wp in
                                                 let uu___15 =
                                                   recheck_debug "_" env3
                                                     item_elab in
                                                 (dmff_env1, item_t, item_wp,
                                                   item_elab)))) in
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      FStar_All.pipe_right ed
                                        FStar_Syntax_Util.get_bind_repr in
                                    FStar_All.pipe_right uu___12
                                      FStar_Util.must in
                                  elaborate_and_star dmff_env [] uu___11 in
                                match uu___10 with
                                | (dmff_env1, uu___11, bind_wp, bind_elab) ->
                                    let uu___12 =
                                      let uu___13 =
                                        let uu___14 =
                                          FStar_All.pipe_right ed
                                            FStar_Syntax_Util.get_return_repr in
                                        FStar_All.pipe_right uu___14
                                          FStar_Util.must in
                                      elaborate_and_star dmff_env1 [] uu___13 in
                                    (match uu___12 with
                                     | (dmff_env2, uu___13, return_wp,
                                        return_elab) ->
                                         let rc_gtot =
                                           {
                                             FStar_Syntax_Syntax.residual_effect
                                               =
                                               FStar_Parser_Const.effect_GTot_lid;
                                             FStar_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStar_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
                                           let uu___14 =
                                             let uu___15 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu___15.FStar_Syntax_Syntax.n in
                                           match uu___14 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs, body, what) ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     FStar_Syntax_Util.abs bs
                                                       body
                                                       FStar_Pervasives_Native.None in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu___17 in
                                                 match uu___16 with
                                                 | (b11::b21::[], body1) ->
                                                     (b11, b21, body1)
                                                 | uu___17 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity" in
                                               (match uu___15 with
                                                | (b11, b21, body1) ->
                                                    let env0 =
                                                      let uu___16 =
                                                        get_env dmff_env2 in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu___16 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu___16 =
                                                          let uu___17 =
                                                            let uu___18 =
                                                              let uu___19 =
                                                                let uu___20 =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b11.FStar_Syntax_Syntax.binder_bv in
                                                                let uu___21 =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false in
                                                                (uu___20,
                                                                  uu___21) in
                                                              [uu___19] in
                                                            (wp_type,
                                                              uu___18) in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu___17 in
                                                        mk uu___16 in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu___16 =
                                                      let uu___17 =
                                                        let uu___18 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1 uu___18 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu___17 in
                                                    (match uu___16 with
                                                     | (bs1, body2, what') ->
                                                         let fail uu___17 =
                                                           let error_msg =
                                                             let uu___18 =
                                                               FStar_Syntax_Print.term_to_string
                                                                 body2 in
                                                             let uu___19 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStar_Ident.string_of_lid
                                                                    rc.FStar_Syntax_Syntax.residual_effect in
                                                             FStar_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu___18
                                                               uu___19 in
                                                           raise_error
                                                             (FStar_Errors.Fatal_WrongBodyTypeForReturnWP,
                                                               error_msg) in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                               -> fail ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu___19
                                                                   =
                                                                   let uu___20
                                                                    =
                                                                    FStar_Syntax_Util.is_pure_effect
                                                                    rc.FStar_Syntax_Syntax.residual_effect in
                                                                   Prims.op_Negation
                                                                    uu___20 in
                                                                 if uu___19
                                                                 then fail ()
                                                                 else ());
                                                                (let uu___19
                                                                   =
                                                                   FStar_Util.map_opt
                                                                    rc.FStar_Syntax_Syntax.residual_typ
                                                                    (fun rt
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStar_TypeChecker_Rel.try_teq
                                                                    true env2
                                                                    rt
                                                                    FStar_Syntax_Util.ktype0 in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env2 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    fail ()) in
                                                                 FStar_All.pipe_right
                                                                   uu___19
                                                                   (fun
                                                                    uu___20
                                                                    -> ()))));
                                                          (let wp =
                                                             let t2 =
                                                               (b21.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               double_star t2 in
                                                             FStar_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type in
                                                           let body3 =
                                                             let uu___18 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp in
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 let uu___21
                                                                   =
                                                                   FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                 (uu___21,
                                                                   FStar_Pervasives_Native.None) in
                                                               [uu___20] in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu___18
                                                               uu___19
                                                               ed_range in
                                                           let uu___18 =
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu___20] in
                                                             b11 :: uu___19 in
                                                           let uu___19 =
                                                             FStar_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStar_Syntax_Util.abs
                                                             uu___18 uu___19
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu___15 ->
                                               raise_error
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let return_wp1 =
                                           let uu___14 =
                                             let uu___15 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp in
                                             uu___15.FStar_Syntax_Syntax.n in
                                           match uu___14 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs, body, what) ->
                                               let uu___15 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu___15
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu___15 ->
                                               raise_error
                                                 (FStar_Errors.Fatal_UnexpectedReturnShape,
                                                   "unexpected shape for return") in
                                         let bind_wp1 =
                                           let uu___14 =
                                             let uu___15 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp in
                                             uu___15.FStar_Syntax_Syntax.n in
                                           match uu___14 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders, body, what) ->
                                               FStar_Syntax_Util.abs binders
                                                 body what
                                           | uu___15 ->
                                               raise_error
                                                 (FStar_Errors.Fatal_UnexpectedBindShape,
                                                   "unexpected shape for bind") in
                                         let apply_close t =
                                           if
                                             (FStar_List.length
                                                effect_binders1)
                                               = Prims.int_zero
                                           then t
                                           else
                                             (let uu___15 =
                                                let uu___16 =
                                                  let uu___17 =
                                                    let uu___18 =
                                                      let uu___19 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu___19 in
                                                    (t, uu___18) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu___17 in
                                                mk uu___16 in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu___15) in
                                         let rec apply_last f l =
                                           match l with
                                           | [] ->
                                               failwith
                                                 "impossible: empty path.."
                                           | a2::[] ->
                                               let uu___14 = f a2 in
                                               [uu___14]
                                           | x::xs ->
                                               let uu___14 = apply_last f xs in
                                               x :: uu___14 in
                                         let register maybe_admit name item =
                                           let maybe_admit1 = true in
                                           let p =
                                             FStar_Ident.path_of_lid
                                               ed.FStar_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last
                                               (fun s ->
                                                  Prims.op_Hat "__"
                                                    (Prims.op_Hat s
                                                       (Prims.op_Hat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStar_Ident.lid_of_path p'
                                               ed_range in
                                           let uu___14 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env2 l' in
                                           match uu___14 with
                                           | FStar_Pervasives_Native.Some
                                               (_us, _t) ->
                                               ((let uu___16 =
                                                   FStar_Options.debug_any () in
                                                 if uu___16
                                                 then
                                                   let uu___17 =
                                                     FStar_Ident.string_of_lid
                                                       l' in
                                                   FStar_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu___17
                                                 else ());
                                                (let uu___16 =
                                                   FStar_Syntax_Syntax.lid_as_fv
                                                     l'
                                                     FStar_Syntax_Syntax.delta_equational
                                                     FStar_Pervasives_Native.None in
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                   uu___16))
                                           | FStar_Pervasives_Native.None ->
                                               let uu___15 =
                                                 let uu___16 = mk_lid name in
                                                 let uu___17 =
                                                   FStar_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 FStar_TypeChecker_Util.mk_toplevel_definition
                                                   env2 uu___16 uu___17 in
                                               (match uu___15 with
                                                | (sigelt, fv) ->
                                                    let sigelt1 =
                                                      if maybe_admit1
                                                      then
                                                        let uu___16 = sigelt in
                                                        {
                                                          FStar_Syntax_Syntax.sigel
                                                            =
                                                            (uu___16.FStar_Syntax_Syntax.sigel);
                                                          FStar_Syntax_Syntax.sigrng
                                                            =
                                                            (uu___16.FStar_Syntax_Syntax.sigrng);
                                                          FStar_Syntax_Syntax.sigquals
                                                            =
                                                            (uu___16.FStar_Syntax_Syntax.sigquals);
                                                          FStar_Syntax_Syntax.sigmeta
                                                            =
                                                            (let uu___17 =
                                                               sigelt.FStar_Syntax_Syntax.sigmeta in
                                                             {
                                                               FStar_Syntax_Syntax.sigmeta_active
                                                                 =
                                                                 (uu___17.FStar_Syntax_Syntax.sigmeta_active);
                                                               FStar_Syntax_Syntax.sigmeta_fact_db_ids
                                                                 =
                                                                 (uu___17.FStar_Syntax_Syntax.sigmeta_fact_db_ids);
                                                               FStar_Syntax_Syntax.sigmeta_admit
                                                                 = true
                                                             });
                                                          FStar_Syntax_Syntax.sigattrs
                                                            =
                                                            (uu___16.FStar_Syntax_Syntax.sigattrs);
                                                          FStar_Syntax_Syntax.sigopts
                                                            =
                                                            (uu___16.FStar_Syntax_Syntax.sigopts)
                                                        }
                                                      else sigelt in
                                                    ((let uu___17 =
                                                        let uu___18 =
                                                          FStar_ST.op_Bang
                                                            sigelts in
                                                        sigelt1 :: uu___18 in
                                                      FStar_ST.op_Colon_Equals
                                                        sigelts uu___17);
                                                     fv)) in
                                         let register_admit = register true in
                                         let register1 = register false in
                                         let lift_from_pure_wp1 =
                                           register1 "lift_from_pure"
                                             lift_from_pure_wp in
                                         let mk_sigelt se =
                                           let uu___14 =
                                             FStar_Syntax_Syntax.mk_sigelt se in
                                           {
                                             FStar_Syntax_Syntax.sigel =
                                               (uu___14.FStar_Syntax_Syntax.sigel);
                                             FStar_Syntax_Syntax.sigrng =
                                               ed_range;
                                             FStar_Syntax_Syntax.sigquals =
                                               (uu___14.FStar_Syntax_Syntax.sigquals);
                                             FStar_Syntax_Syntax.sigmeta =
                                               (uu___14.FStar_Syntax_Syntax.sigmeta);
                                             FStar_Syntax_Syntax.sigattrs =
                                               (uu___14.FStar_Syntax_Syntax.sigattrs);
                                             FStar_Syntax_Syntax.sigopts =
                                               (uu___14.FStar_Syntax_Syntax.sigopts)
                                           } in
                                         let return_wp2 =
                                           register1 "return_wp" return_wp1 in
                                         let return_elab1 =
                                           register_admit "return_elab"
                                             return_elab in
                                         let bind_wp2 =
                                           register1 "bind_wp" bind_wp1 in
                                         let bind_elab1 =
                                           register_admit "bind_elab"
                                             bind_elab in
                                         let uu___14 =
                                           FStar_List.fold_left
                                             (fun uu___15 ->
                                                fun action ->
                                                  match uu___15 with
                                                  | (dmff_env3, actions) ->
                                                      let params_un =
                                                        FStar_Syntax_Subst.open_binders
                                                          action.FStar_Syntax_Syntax.action_params in
                                                      let uu___16 =
                                                        let uu___17 =
                                                          get_env dmff_env3 in
                                                        FStar_TypeChecker_TcTerm.tc_tparams
                                                          uu___17 params_un in
                                                      (match uu___16 with
                                                       | (action_params,
                                                          env', uu___17) ->
                                                           let action_params1
                                                             =
                                                             FStar_List.map
                                                               (fun b ->
                                                                  let uu___18
                                                                    = b in
                                                                  let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    b.FStar_Syntax_Syntax.binder_bv in
                                                                    let uu___21
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___20.FStar_Syntax_Syntax.ppname);
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (uu___20.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    = uu___21
                                                                    } in
                                                                  {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = uu___19;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (uu___18.FStar_Syntax_Syntax.binder_qual);
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (uu___18.FStar_Syntax_Syntax.binder_attrs)
                                                                  })
                                                               action_params in
                                                           let dmff_env' =
                                                             set_env
                                                               dmff_env3 env' in
                                                           let uu___18 =
                                                             elaborate_and_star
                                                               dmff_env'
                                                               action_params1
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn)) in
                                                           (match uu___18
                                                            with
                                                            | (dmff_env4,
                                                               action_t,
                                                               action_wp,
                                                               action_elab)
                                                                ->
                                                                let name =
                                                                  let uu___19
                                                                    =
                                                                    FStar_Ident.ident_of_lid
                                                                    action.FStar_Syntax_Syntax.action_name in
                                                                  FStar_Ident.string_of_id
                                                                    uu___19 in
                                                                let action_typ_with_wp
                                                                  =
                                                                  trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp in
                                                                let action_params2
                                                                  =
                                                                  FStar_Syntax_Subst.close_binders
                                                                    action_params1 in
                                                                let action_elab1
                                                                  =
                                                                  FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab in
                                                                let action_typ_with_wp1
                                                                  =
                                                                  FStar_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp in
                                                                let action_elab2
                                                                  =
                                                                  FStar_Syntax_Util.abs
                                                                    action_params2
                                                                    action_elab1
                                                                    FStar_Pervasives_Native.None in
                                                                let action_typ_with_wp2
                                                                  =
                                                                  match action_params2
                                                                  with
                                                                  | [] ->
                                                                    action_typ_with_wp1
                                                                  | uu___19
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStar_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu___20 in
                                                                ((let uu___20
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "ED") in
                                                                  if uu___20
                                                                  then
                                                                    let uu___21
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    params_un in
                                                                    let uu___22
                                                                    =
                                                                    FStar_Syntax_Print.binders_to_string
                                                                    ","
                                                                    action_params2 in
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_typ_with_wp2 in
                                                                    let uu___24
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    action_elab2 in
                                                                    FStar_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu___21
                                                                    uu___22
                                                                    uu___23
                                                                    uu___24
                                                                  else ());
                                                                 (let action_elab3
                                                                    =
                                                                    register1
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                  let action_typ_with_wp3
                                                                    =
                                                                    register1
                                                                    (Prims.op_Hat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                  let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    = action in
                                                                    let uu___23
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu___24
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___22.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___22.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___22.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    = uu___23;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    = uu___24
                                                                    } in
                                                                    uu___21
                                                                    ::
                                                                    actions in
                                                                  (dmff_env4,
                                                                    uu___20))))))
                                             (dmff_env2, [])
                                             ed.FStar_Syntax_Syntax.actions in
                                         (match uu___14 with
                                          | (dmff_env3, actions) ->
                                              let actions1 =
                                                FStar_List.rev actions in
                                              let repr1 =
                                                let wp =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "wp_a"
                                                    FStar_Pervasives_Native.None
                                                    wp_a in
                                                let binders =
                                                  let uu___15 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a1 in
                                                  let uu___16 =
                                                    let uu___17 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        wp in
                                                    [uu___17] in
                                                  uu___15 :: uu___16 in
                                                let uu___15 =
                                                  let uu___16 =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        let uu___19 =
                                                          let uu___20 =
                                                            let uu___21 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a1 in
                                                            let uu___22 =
                                                              FStar_Syntax_Syntax.as_implicit
                                                                false in
                                                            (uu___21,
                                                              uu___22) in
                                                          [uu___20] in
                                                        (repr, uu___19) in
                                                      FStar_Syntax_Syntax.Tm_app
                                                        uu___18 in
                                                    mk uu___17 in
                                                  let uu___17 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      wp in
                                                  trans_F dmff_env3 uu___16
                                                    uu___17 in
                                                FStar_Syntax_Util.abs binders
                                                  uu___15
                                                  FStar_Pervasives_Native.None in
                                              let uu___15 =
                                                recheck_debug "FC" env2 repr1 in
                                              let repr2 =
                                                register1 "repr" repr1 in
                                              let uu___16 =
                                                let uu___17 =
                                                  let uu___18 =
                                                    let uu___19 =
                                                      FStar_Syntax_Subst.compress
                                                        wp_type in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.unascribe
                                                      uu___19 in
                                                  uu___18.FStar_Syntax_Syntax.n in
                                                match uu___17 with
                                                | FStar_Syntax_Syntax.Tm_abs
                                                    (type_param::effect_param,
                                                     arrow, uu___18)
                                                    ->
                                                    let uu___19 =
                                                      let uu___20 =
                                                        FStar_Syntax_Subst.open_term
                                                          (type_param ::
                                                          effect_param) arrow in
                                                      match uu___20 with
                                                      | (b::bs, body) ->
                                                          (b, bs, body)
                                                      | uu___21 ->
                                                          failwith
                                                            "Impossible : open_term nt preserving binders arity" in
                                                    (match uu___19 with
                                                     | (type_param1,
                                                        effect_param1,
                                                        arrow1) ->
                                                         let uu___20 =
                                                           let uu___21 =
                                                             let uu___22 =
                                                               FStar_Syntax_Subst.compress
                                                                 arrow1 in
                                                             FStar_All.pipe_left
                                                               FStar_Syntax_Util.unascribe
                                                               uu___22 in
                                                           uu___21.FStar_Syntax_Syntax.n in
                                                         (match uu___20 with
                                                          | FStar_Syntax_Syntax.Tm_arrow
                                                              (wp_binders, c)
                                                              ->
                                                              let uu___21 =
                                                                FStar_Syntax_Subst.open_comp
                                                                  wp_binders
                                                                  c in
                                                              (match uu___21
                                                               with
                                                               | (wp_binders1,
                                                                  c1) ->
                                                                   let uu___22
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___24;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___25;_}
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort in
                                                                    FStar_All.pipe_right
                                                                    uu___27
                                                                    (FStar_Util.set_mem
                                                                    type_param1.FStar_Syntax_Syntax.binder_bv) in
                                                                    FStar_All.pipe_right
                                                                    uu___26
                                                                    Prims.op_Negation)
                                                                    wp_binders1 in
                                                                   (match uu___22
                                                                    with
                                                                    | 
                                                                    (pre_args,
                                                                    post_args)
                                                                    ->
                                                                    let post
                                                                    =
                                                                    match post_args
                                                                    with
                                                                    | 
                                                                    post1::[]
                                                                    -> post1
                                                                    | 
                                                                    [] ->
                                                                    let err_msg
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu___23 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg)
                                                                    | 
                                                                    uu___23
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1 in
                                                                    FStar_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu___24 in
                                                                    FStar_Errors.raise_err
                                                                    (FStar_Errors.Fatal_ImpossibleToGenerateDMEffect,
                                                                    err_msg) in
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu___24
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (post.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu___23,
                                                                    uu___24)))
                                                          | uu___21 ->
                                                              let uu___22 =
                                                                let uu___23 =
                                                                  let uu___24
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow1 in
                                                                  FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu___24 in
                                                                (FStar_Errors.Fatal_ImpossiblePrePostArrow,
                                                                  uu___23) in
                                                              raise_error
                                                                uu___22))
                                                | uu___18 ->
                                                    let uu___19 =
                                                      let uu___20 =
                                                        let uu___21 =
                                                          FStar_Syntax_Print.term_to_string
                                                            wp_type in
                                                        FStar_Util.format1
                                                          "Impossible: pre/post abs %s"
                                                          uu___21 in
                                                      (FStar_Errors.Fatal_ImpossiblePrePostAbs,
                                                        uu___20) in
                                                    raise_error uu___19 in
                                              (match uu___16 with
                                               | (pre, post) ->
                                                   ((let uu___18 =
                                                       register1 "pre" pre in
                                                     ());
                                                    (let uu___19 =
                                                       register1 "post" post in
                                                     ());
                                                    (let uu___20 =
                                                       register1 "wp" wp_type in
                                                     ());
                                                    (let ed_combs =
                                                       match ed.FStar_Syntax_Syntax.combinators
                                                       with
                                                       | FStar_Syntax_Syntax.DM4F_eff
                                                           combs ->
                                                           let uu___20 =
                                                             let uu___21 =
                                                               combs in
                                                             let uu___22 =
                                                               let uu___23 =
                                                                 apply_close
                                                                   return_wp2 in
                                                               ([], uu___23) in
                                                             let uu___23 =
                                                               let uu___24 =
                                                                 apply_close
                                                                   bind_wp2 in
                                                               ([], uu___24) in
                                                             let uu___24 =
                                                               let uu___25 =
                                                                 let uu___26
                                                                   =
                                                                   apply_close
                                                                    repr2 in
                                                                 ([],
                                                                   uu___26) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___25 in
                                                             let uu___25 =
                                                               let uu___26 =
                                                                 let uu___27
                                                                   =
                                                                   apply_close
                                                                    return_elab1 in
                                                                 ([],
                                                                   uu___27) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___26 in
                                                             let uu___26 =
                                                               let uu___27 =
                                                                 let uu___28
                                                                   =
                                                                   apply_close
                                                                    bind_elab1 in
                                                                 ([],
                                                                   uu___28) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___27 in
                                                             {
                                                               FStar_Syntax_Syntax.ret_wp
                                                                 = uu___22;
                                                               FStar_Syntax_Syntax.bind_wp
                                                                 = uu___23;
                                                               FStar_Syntax_Syntax.stronger
                                                                 =
                                                                 (uu___21.FStar_Syntax_Syntax.stronger);
                                                               FStar_Syntax_Syntax.if_then_else
                                                                 =
                                                                 (uu___21.FStar_Syntax_Syntax.if_then_else);
                                                               FStar_Syntax_Syntax.ite_wp
                                                                 =
                                                                 (uu___21.FStar_Syntax_Syntax.ite_wp);
                                                               FStar_Syntax_Syntax.close_wp
                                                                 =
                                                                 (uu___21.FStar_Syntax_Syntax.close_wp);
                                                               FStar_Syntax_Syntax.trivial
                                                                 =
                                                                 (uu___21.FStar_Syntax_Syntax.trivial);
                                                               FStar_Syntax_Syntax.repr
                                                                 = uu___24;
                                                               FStar_Syntax_Syntax.return_repr
                                                                 = uu___25;
                                                               FStar_Syntax_Syntax.bind_repr
                                                                 = uu___26
                                                             } in
                                                           FStar_Syntax_Syntax.DM4F_eff
                                                             uu___20
                                                       | uu___20 ->
                                                           failwith
                                                             "Impossible! For a DM4F effect combinators must be in DM4f_eff" in
                                                     let ed1 =
                                                       let uu___20 = ed in
                                                       let uu___21 =
                                                         FStar_Syntax_Subst.close_binders
                                                           effect_binders1 in
                                                       let uu___22 =
                                                         let uu___23 =
                                                           FStar_Syntax_Subst.close
                                                             effect_binders1
                                                             effect_signature in
                                                         ([], uu___23) in
                                                       {
                                                         FStar_Syntax_Syntax.mname
                                                           =
                                                           (uu___20.FStar_Syntax_Syntax.mname);
                                                         FStar_Syntax_Syntax.cattributes
                                                           =
                                                           (uu___20.FStar_Syntax_Syntax.cattributes);
                                                         FStar_Syntax_Syntax.univs
                                                           =
                                                           (uu___20.FStar_Syntax_Syntax.univs);
                                                         FStar_Syntax_Syntax.binders
                                                           = uu___21;
                                                         FStar_Syntax_Syntax.signature
                                                           = uu___22;
                                                         FStar_Syntax_Syntax.combinators
                                                           = ed_combs;
                                                         FStar_Syntax_Syntax.actions
                                                           = actions1;
                                                         FStar_Syntax_Syntax.eff_attrs
                                                           =
                                                           (uu___20.FStar_Syntax_Syntax.eff_attrs)
                                                       } in
                                                     let uu___20 =
                                                       gen_wps_for_free env2
                                                         effect_binders1 a1
                                                         wp_a ed1 in
                                                     match uu___20 with
                                                     | (sigelts', ed2) ->
                                                         ((let uu___22 =
                                                             FStar_TypeChecker_Env.debug
                                                               env2
                                                               (FStar_Options.Other
                                                                  "ED") in
                                                           if uu___22
                                                           then
                                                             let uu___23 =
                                                               FStar_Syntax_Print.eff_decl_to_string
                                                                 true ed2 in
                                                             FStar_Util.print_string
                                                               uu___23
                                                           else ());
                                                          (let lift_from_pure_opt
                                                             =
                                                             if
                                                               (FStar_List.length
                                                                  effect_binders1)
                                                                 =
                                                                 Prims.int_zero
                                                             then
                                                               let lift_from_pure
                                                                 =
                                                                 let uu___22
                                                                   =
                                                                   let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1 in
                                                                    ([],
                                                                    uu___24) in
                                                                   FStar_Pervasives_Native.Some
                                                                    uu___23 in
                                                                 {
                                                                   FStar_Syntax_Syntax.source
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                   FStar_Syntax_Syntax.lift_wp
                                                                    = uu___22;
                                                                   FStar_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                 } in
                                                               let uu___22 =
                                                                 mk_sigelt
                                                                   (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___22
                                                             else
                                                               FStar_Pervasives_Native.None in
                                                           let uu___22 =
                                                             let uu___23 =
                                                               let uu___24 =
                                                                 FStar_ST.op_Bang
                                                                   sigelts in
                                                               FStar_List.rev
                                                                 uu___24 in
                                                             FStar_List.append
                                                               uu___23
                                                               sigelts' in
                                                           (uu___22, ed2,
                                                             lift_from_pure_opt))))))))))))))