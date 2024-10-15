open Prims
type env =
  {
  tcenv: FStarC_TypeChecker_Env.env ;
  subst: FStarC_Syntax_Syntax.subst_elt Prims.list ;
  tc_const: FStarC_Const.sconst -> FStarC_Syntax_Syntax.typ }
let (__proj__Mkenv__item__tcenv : env -> FStarC_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> tcenv
let (__proj__Mkenv__item__subst :
  env -> FStarC_Syntax_Syntax.subst_elt Prims.list) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> subst
let (__proj__Mkenv__item__tc_const :
  env -> FStarC_Const.sconst -> FStarC_Syntax_Syntax.typ) =
  fun projectee ->
    match projectee with | { tcenv; subst; tc_const;_} -> tc_const
let (dbg : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "ED"
let (d : Prims.string -> unit) =
  fun s -> FStarC_Compiler_Util.print1 "\027[01;36m%s\027[00m\n" s
let (mk_toplevel_definition :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.term ->
        (FStarC_Syntax_Syntax.sigelt * FStarC_Syntax_Syntax.term))
  =
  fun env1 ->
    fun lident ->
      fun def ->
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg in
         if uu___1
         then
           ((let uu___3 = FStarC_Ident.string_of_lid lident in d uu___3);
            (let uu___3 =
               FStarC_Class_Show.show FStarC_Ident.showable_lident lident in
             let uu___4 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term def in
             FStarC_Compiler_Util.print2
               "Registering top-level definition: %s\n%s\n" uu___3 uu___4))
         else ());
        (let fv =
           FStarC_Syntax_Syntax.lid_and_dd_as_fv lident
             FStar_Pervasives_Native.None in
         let lbname = FStar_Pervasives.Inr fv in
         let lb =
           (false,
             [FStarC_Syntax_Util.mk_letbinding lbname []
                FStarC_Syntax_Syntax.tun FStarC_Parser_Const.effect_Tot_lid
                def [] FStarC_Compiler_Range_Type.dummyRange]) in
         let sig_ctx =
           FStarC_Syntax_Syntax.mk_sigelt
             (FStarC_Syntax_Syntax.Sig_let
                {
                  FStarC_Syntax_Syntax.lbs1 = lb;
                  FStarC_Syntax_Syntax.lids1 = [lident]
                }) in
         let uu___1 =
           FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_fvar fv)
             FStarC_Compiler_Range_Type.dummyRange in
         ({
            FStarC_Syntax_Syntax.sigel = (sig_ctx.FStarC_Syntax_Syntax.sigel);
            FStarC_Syntax_Syntax.sigrng =
              (sig_ctx.FStarC_Syntax_Syntax.sigrng);
            FStarC_Syntax_Syntax.sigquals =
              [FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen];
            FStarC_Syntax_Syntax.sigmeta =
              (sig_ctx.FStarC_Syntax_Syntax.sigmeta);
            FStarC_Syntax_Syntax.sigattrs =
              (sig_ctx.FStarC_Syntax_Syntax.sigattrs);
            FStarC_Syntax_Syntax.sigopens_and_abbrevs =
              (sig_ctx.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
            FStarC_Syntax_Syntax.sigopts =
              (sig_ctx.FStarC_Syntax_Syntax.sigopts)
          }, uu___1))
let (empty :
  FStarC_TypeChecker_Env.env ->
    (FStarC_Const.sconst -> FStarC_Syntax_Syntax.typ) -> env)
  = fun env1 -> fun tc_const -> { tcenv = env1; subst = []; tc_const }
let (gen_wps_for_free :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binders ->
      FStarC_Syntax_Syntax.bv ->
        FStarC_Syntax_Syntax.term ->
          FStarC_Syntax_Syntax.eff_decl ->
            (FStarC_Syntax_Syntax.sigelts * FStarC_Syntax_Syntax.eff_decl))
  =
  fun env1 ->
    fun binders ->
      fun a ->
        fun wp_a ->
          fun ed ->
            let wp_a1 =
              FStarC_TypeChecker_Normalize.normalize
                [FStarC_TypeChecker_Env.Beta;
                FStarC_TypeChecker_Env.EraseUniverses] env1 wp_a in
            let a1 =
              let uu___ =
                FStarC_TypeChecker_Normalize.normalize
                  [FStarC_TypeChecker_Env.EraseUniverses] env1
                  a.FStarC_Syntax_Syntax.sort in
              {
                FStarC_Syntax_Syntax.ppname = (a.FStarC_Syntax_Syntax.ppname);
                FStarC_Syntax_Syntax.index = (a.FStarC_Syntax_Syntax.index);
                FStarC_Syntax_Syntax.sort = uu___
              } in
            let d1 s =
              FStarC_Compiler_Util.print1 "\027[01;36m%s\027[00m\n" s in
            (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg in
             if uu___1
             then
               (d1 "Elaborating extra WP combinators";
                (let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     wp_a1 in
                 FStarC_Compiler_Util.print1 "wp_a is: %s\n" uu___3))
             else ());
            (let rec collect_binders t =
               let t1 = FStarC_Syntax_Util.unascribe t in
               let uu___1 =
                 let uu___2 = FStarC_Syntax_Subst.compress t1 in
                 uu___2.FStarC_Syntax_Syntax.n in
               match uu___1 with
               | FStarC_Syntax_Syntax.Tm_arrow
                   { FStarC_Syntax_Syntax.bs1 = bs;
                     FStarC_Syntax_Syntax.comp = comp;_}
                   ->
                   let rest =
                     match comp.FStarC_Syntax_Syntax.n with
                     | FStarC_Syntax_Syntax.Total t2 -> t2
                     | uu___2 ->
                         let uu___3 =
                           let uu___4 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_comp comp in
                           FStarC_Compiler_Util.format1
                             "wp_a contains non-Tot arrow: %s" uu___4 in
                         FStarC_Errors.raise_error
                           (FStarC_Syntax_Syntax.has_range_syntax ()) comp
                           FStarC_Errors_Codes.Error_UnexpectedDM4FType ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_string)
                           (Obj.magic uu___3) in
                   let uu___2 = collect_binders rest in
                   FStarC_Compiler_List.op_At bs uu___2
               | FStarC_Syntax_Syntax.Tm_type uu___2 -> []
               | uu___2 ->
                   let uu___3 =
                     let uu___4 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term t1 in
                     FStarC_Compiler_Util.format1
                       "wp_a doesn't end in Type0, but rather in %s" uu___4 in
                   FStarC_Errors.raise_error
                     (FStarC_Syntax_Syntax.has_range_syntax ()) t1
                     FStarC_Errors_Codes.Error_UnexpectedDM4FType ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___3) in
             let mk_lid name = FStarC_Syntax_Util.dm4f_lid ed name in
             let gamma =
               let uu___1 = collect_binders wp_a1 in
               FStarC_Syntax_Util.name_binders uu___1 in
             (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg in
              if uu___2
              then
                let uu___3 =
                  let uu___4 =
                    FStarC_Class_Show.show
                      (FStarC_Class_Show.show_list
                         FStarC_Syntax_Print.showable_binder) gamma in
                  FStarC_Compiler_Util.format1 "Gamma is %s\n" uu___4 in
                d1 uu___3
              else ());
             (let unknown = FStarC_Syntax_Syntax.tun in
              let mk x =
                FStarC_Syntax_Syntax.mk x
                  FStarC_Compiler_Range_Type.dummyRange in
              let sigelts = FStarC_Compiler_Util.mk_ref [] in
              let register env2 lident def =
                let uu___2 = mk_toplevel_definition env2 lident def in
                match uu___2 with
                | (sigelt, fv) ->
                    let sigelt1 =
                      {
                        FStarC_Syntax_Syntax.sigel =
                          (sigelt.FStarC_Syntax_Syntax.sigel);
                        FStarC_Syntax_Syntax.sigrng =
                          (sigelt.FStarC_Syntax_Syntax.sigrng);
                        FStarC_Syntax_Syntax.sigquals =
                          (sigelt.FStarC_Syntax_Syntax.sigquals);
                        FStarC_Syntax_Syntax.sigmeta =
                          (let uu___3 = sigelt.FStarC_Syntax_Syntax.sigmeta in
                           {
                             FStarC_Syntax_Syntax.sigmeta_active =
                               (uu___3.FStarC_Syntax_Syntax.sigmeta_active);
                             FStarC_Syntax_Syntax.sigmeta_fact_db_ids =
                               (uu___3.FStarC_Syntax_Syntax.sigmeta_fact_db_ids);
                             FStarC_Syntax_Syntax.sigmeta_admit = true;
                             FStarC_Syntax_Syntax.sigmeta_spliced =
                               (uu___3.FStarC_Syntax_Syntax.sigmeta_spliced);
                             FStarC_Syntax_Syntax.sigmeta_already_checked =
                               (uu___3.FStarC_Syntax_Syntax.sigmeta_already_checked);
                             FStarC_Syntax_Syntax.sigmeta_extension_data =
                               (uu___3.FStarC_Syntax_Syntax.sigmeta_extension_data)
                           });
                        FStarC_Syntax_Syntax.sigattrs =
                          (sigelt.FStarC_Syntax_Syntax.sigattrs);
                        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                          (sigelt.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                        FStarC_Syntax_Syntax.sigopts =
                          (sigelt.FStarC_Syntax_Syntax.sigopts)
                      } in
                    ((let uu___4 =
                        let uu___5 = FStarC_Compiler_Effect.op_Bang sigelts in
                        sigelt1 :: uu___5 in
                      FStarC_Compiler_Effect.op_Colon_Equals sigelts uu___4);
                     fv) in
              let binders_of_list =
                FStarC_Compiler_List.map
                  (fun uu___2 ->
                     match uu___2 with
                     | (t, b) ->
                         let uu___3 =
                           FStarC_Syntax_Syntax.as_bqual_implicit b in
                         FStarC_Syntax_Syntax.mk_binder_with_attrs t uu___3
                           FStar_Pervasives_Native.None []) in
              let mk_all_implicit =
                FStarC_Compiler_List.map
                  (fun t ->
                     let uu___2 = FStarC_Syntax_Syntax.as_bqual_implicit true in
                     {
                       FStarC_Syntax_Syntax.binder_bv =
                         (t.FStarC_Syntax_Syntax.binder_bv);
                       FStarC_Syntax_Syntax.binder_qual = uu___2;
                       FStarC_Syntax_Syntax.binder_positivity =
                         (t.FStarC_Syntax_Syntax.binder_positivity);
                       FStarC_Syntax_Syntax.binder_attrs =
                         (t.FStarC_Syntax_Syntax.binder_attrs)
                     }) in
              let args_of_binders =
                FStarC_Compiler_List.map
                  (fun bv ->
                     let uu___2 =
                       FStarC_Syntax_Syntax.bv_to_name
                         bv.FStarC_Syntax_Syntax.binder_bv in
                     FStarC_Syntax_Syntax.as_arg uu___2) in
              let uu___2 =
                let uu___3 =
                  let mk1 f =
                    let t =
                      FStarC_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let body =
                      let uu___4 =
                        let uu___5 = FStarC_Syntax_Syntax.bv_to_name t in
                        f uu___5 in
                      FStarC_Syntax_Util.arrow gamma uu___4 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStarC_Syntax_Syntax.mk_binder a1 in
                        let uu___7 =
                          let uu___8 = FStarC_Syntax_Syntax.mk_binder t in
                          [uu___8] in
                        uu___6 :: uu___7 in
                      FStarC_Compiler_List.op_At binders uu___5 in
                    FStarC_Syntax_Util.abs uu___4 body
                      FStar_Pervasives_Native.None in
                  let uu___4 = mk1 FStarC_Syntax_Syntax.mk_Total in
                  let uu___5 = mk1 FStarC_Syntax_Syntax.mk_GTotal in
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
                              FStarC_Compiler_List.map
                                (fun uu___8 ->
                                   match uu___8 with
                                   | { FStarC_Syntax_Syntax.binder_bv = bv;
                                       FStarC_Syntax_Syntax.binder_qual =
                                         uu___9;
                                       FStarC_Syntax_Syntax.binder_positivity
                                         = uu___10;
                                       FStarC_Syntax_Syntax.binder_attrs =
                                         uu___11;_}
                                       ->
                                       let uu___12 =
                                         FStarC_Syntax_Syntax.bv_to_name bv in
                                       let uu___13 =
                                         FStarC_Syntax_Syntax.as_aqual_implicit
                                           false in
                                       (uu___12, uu___13)) binders in
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  FStarC_Syntax_Syntax.bv_to_name a1 in
                                let uu___11 =
                                  FStarC_Syntax_Syntax.as_aqual_implicit
                                    false in
                                (uu___10, uu___11) in
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStarC_Syntax_Syntax.as_aqual_implicit
                                      false in
                                  (t, uu___12) in
                                [uu___11] in
                              uu___9 :: uu___10 in
                            FStarC_Compiler_List.op_At uu___7 uu___8 in
                          {
                            FStarC_Syntax_Syntax.hd = fv;
                            FStarC_Syntax_Syntax.args = uu___6
                          } in
                        FStarC_Syntax_Syntax.Tm_app uu___5 in
                      mk uu___4 in
                    (env1, (mk_app ctx_fv), (mk_app gctx_fv)) in
              match uu___2 with
              | (env2, mk_ctx, mk_gctx) ->
                  let c_pure =
                    let t =
                      FStarC_Syntax_Syntax.gen_bv "t"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let x =
                      let uu___3 = FStarC_Syntax_Syntax.bv_to_name t in
                      FStarC_Syntax_Syntax.gen_bv "x"
                        FStar_Pervasives_Native.None uu___3 in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name t in
                          mk_ctx uu___5 in
                        FStarC_Syntax_Util.residual_tot uu___4 in
                      FStar_Pervasives_Native.Some uu___3 in
                    let body =
                      let uu___3 = FStarC_Syntax_Syntax.bv_to_name x in
                      FStarC_Syntax_Util.abs gamma uu___3 ret in
                    let uu___3 =
                      let uu___4 = mk_all_implicit binders in
                      let uu___5 =
                        binders_of_list [(a1, true); (t, true); (x, false)] in
                      FStarC_Compiler_List.op_At uu___4 uu___5 in
                    FStarC_Syntax_Util.abs uu___3 body ret in
                  let c_pure1 =
                    let uu___3 = mk_lid "pure" in register env2 uu___3 c_pure in
                  let c_app =
                    let t1 =
                      FStarC_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t2 =
                      FStarC_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let l =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  FStarC_Syntax_Syntax.bv_to_name t1 in
                                FStarC_Syntax_Syntax.new_bv
                                  FStar_Pervasives_Native.None uu___8 in
                              FStarC_Syntax_Syntax.mk_binder uu___7 in
                            [uu___6] in
                          let uu___6 =
                            let uu___7 = FStarC_Syntax_Syntax.bv_to_name t2 in
                            FStarC_Syntax_Syntax.mk_GTotal uu___7 in
                          FStarC_Syntax_Util.arrow uu___5 uu___6 in
                        mk_gctx uu___4 in
                      FStarC_Syntax_Syntax.gen_bv "l"
                        FStar_Pervasives_Native.None uu___3 in
                    let r =
                      let uu___3 =
                        let uu___4 = FStarC_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu___4 in
                      FStarC_Syntax_Syntax.gen_bv "r"
                        FStar_Pervasives_Native.None uu___3 in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu___5 in
                        FStarC_Syntax_Util.residual_tot uu___4 in
                      FStar_Pervasives_Native.Some uu___3 in
                    let outer_body =
                      let gamma_as_args = args_of_binders gamma in
                      let inner_body =
                        let uu___3 = FStarC_Syntax_Syntax.bv_to_name l in
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  FStarC_Syntax_Syntax.bv_to_name r in
                                FStarC_Syntax_Util.mk_app uu___8
                                  gamma_as_args in
                              FStarC_Syntax_Syntax.as_arg uu___7 in
                            [uu___6] in
                          FStarC_Compiler_List.op_At gamma_as_args uu___5 in
                        FStarC_Syntax_Util.mk_app uu___3 uu___4 in
                      FStarC_Syntax_Util.abs gamma inner_body ret in
                    let uu___3 =
                      let uu___4 = mk_all_implicit binders in
                      let uu___5 =
                        binders_of_list
                          [(a1, true);
                          (t1, true);
                          (t2, true);
                          (l, false);
                          (r, false)] in
                      FStarC_Compiler_List.op_At uu___4 uu___5 in
                    FStarC_Syntax_Util.abs uu___3 outer_body ret in
                  let c_app1 =
                    let uu___3 = mk_lid "app" in register env2 uu___3 c_app in
                  let c_lift1 =
                    let t1 =
                      FStarC_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t2 =
                      FStarC_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t_f =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name t1 in
                          FStarC_Syntax_Syntax.null_binder uu___5 in
                        [uu___4] in
                      let uu___4 =
                        let uu___5 = FStarC_Syntax_Syntax.bv_to_name t2 in
                        FStarC_Syntax_Syntax.mk_GTotal uu___5 in
                      FStarC_Syntax_Util.arrow uu___3 uu___4 in
                    let f =
                      FStarC_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu___3 =
                        let uu___4 = FStarC_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu___4 in
                      FStarC_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu___3 in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu___5 in
                        FStarC_Syntax_Util.residual_tot uu___4 in
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
                      FStarC_Compiler_List.op_At uu___4 uu___5 in
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  FStarC_Syntax_Syntax.bv_to_name f in
                                [uu___10] in
                              FStarC_Compiler_List.map
                                FStarC_Syntax_Syntax.as_arg uu___9 in
                            FStarC_Syntax_Util.mk_app c_pure1 uu___8 in
                          let uu___8 =
                            let uu___9 = FStarC_Syntax_Syntax.bv_to_name a11 in
                            [uu___9] in
                          uu___7 :: uu___8 in
                        FStarC_Compiler_List.map FStarC_Syntax_Syntax.as_arg
                          uu___6 in
                      FStarC_Syntax_Util.mk_app c_app1 uu___5 in
                    FStarC_Syntax_Util.abs uu___3 uu___4 ret in
                  let c_lift11 =
                    let uu___3 = mk_lid "lift1" in
                    register env2 uu___3 c_lift1 in
                  let c_lift2 =
                    let t1 =
                      FStarC_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t2 =
                      FStarC_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t3 =
                      FStarC_Syntax_Syntax.gen_bv "t3"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t_f =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name t1 in
                          FStarC_Syntax_Syntax.null_binder uu___5 in
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = FStarC_Syntax_Syntax.bv_to_name t2 in
                            FStarC_Syntax_Syntax.null_binder uu___7 in
                          [uu___6] in
                        uu___4 :: uu___5 in
                      let uu___4 =
                        let uu___5 = FStarC_Syntax_Syntax.bv_to_name t3 in
                        FStarC_Syntax_Syntax.mk_GTotal uu___5 in
                      FStarC_Syntax_Util.arrow uu___3 uu___4 in
                    let f =
                      FStarC_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let a11 =
                      let uu___3 =
                        let uu___4 = FStarC_Syntax_Syntax.bv_to_name t1 in
                        mk_gctx uu___4 in
                      FStarC_Syntax_Syntax.gen_bv "a1"
                        FStar_Pervasives_Native.None uu___3 in
                    let a2 =
                      let uu___3 =
                        let uu___4 = FStarC_Syntax_Syntax.bv_to_name t2 in
                        mk_gctx uu___4 in
                      FStarC_Syntax_Syntax.gen_bv "a2"
                        FStar_Pervasives_Native.None uu___3 in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name t3 in
                          mk_gctx uu___5 in
                        FStarC_Syntax_Util.residual_tot uu___4 in
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
                      FStarC_Compiler_List.op_At uu___4 uu___5 in
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
                                        FStarC_Syntax_Syntax.bv_to_name f in
                                      [uu___13] in
                                    FStarC_Compiler_List.map
                                      FStarC_Syntax_Syntax.as_arg uu___12 in
                                  FStarC_Syntax_Util.mk_app c_pure1 uu___11 in
                                let uu___11 =
                                  let uu___12 =
                                    FStarC_Syntax_Syntax.bv_to_name a11 in
                                  [uu___12] in
                                uu___10 :: uu___11 in
                              FStarC_Compiler_List.map
                                FStarC_Syntax_Syntax.as_arg uu___9 in
                            FStarC_Syntax_Util.mk_app c_app1 uu___8 in
                          let uu___8 =
                            let uu___9 = FStarC_Syntax_Syntax.bv_to_name a2 in
                            [uu___9] in
                          uu___7 :: uu___8 in
                        FStarC_Compiler_List.map FStarC_Syntax_Syntax.as_arg
                          uu___6 in
                      FStarC_Syntax_Util.mk_app c_app1 uu___5 in
                    FStarC_Syntax_Util.abs uu___3 uu___4 ret in
                  let c_lift21 =
                    let uu___3 = mk_lid "lift2" in
                    register env2 uu___3 c_lift2 in
                  let c_push =
                    let t1 =
                      FStarC_Syntax_Syntax.gen_bv "t1"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t2 =
                      FStarC_Syntax_Syntax.gen_bv "t2"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t_f =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name t1 in
                          FStarC_Syntax_Syntax.null_binder uu___5 in
                        [uu___4] in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = FStarC_Syntax_Syntax.bv_to_name t2 in
                          mk_gctx uu___6 in
                        FStarC_Syntax_Syntax.mk_Total uu___5 in
                      FStarC_Syntax_Util.arrow uu___3 uu___4 in
                    let f =
                      FStarC_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let ret =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  FStarC_Syntax_Syntax.bv_to_name t1 in
                                FStarC_Syntax_Syntax.null_binder uu___8 in
                              [uu___7] in
                            let uu___7 =
                              let uu___8 = FStarC_Syntax_Syntax.bv_to_name t2 in
                              FStarC_Syntax_Syntax.mk_GTotal uu___8 in
                            FStarC_Syntax_Util.arrow uu___6 uu___7 in
                          mk_ctx uu___5 in
                        FStarC_Syntax_Util.residual_tot uu___4 in
                      FStar_Pervasives_Native.Some uu___3 in
                    let e1 =
                      let uu___3 = FStarC_Syntax_Syntax.bv_to_name t1 in
                      FStarC_Syntax_Syntax.gen_bv "e1"
                        FStar_Pervasives_Native.None uu___3 in
                    let body =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.mk_binder e1 in
                          [uu___5] in
                        FStarC_Compiler_List.op_At gamma uu___4 in
                      let uu___4 =
                        let uu___5 = FStarC_Syntax_Syntax.bv_to_name f in
                        let uu___6 =
                          let uu___7 =
                            let uu___8 = FStarC_Syntax_Syntax.bv_to_name e1 in
                            FStarC_Syntax_Syntax.as_arg uu___8 in
                          let uu___8 = args_of_binders gamma in uu___7 ::
                            uu___8 in
                        FStarC_Syntax_Util.mk_app uu___5 uu___6 in
                      FStarC_Syntax_Util.abs uu___3 uu___4 ret in
                    let uu___3 =
                      let uu___4 = mk_all_implicit binders in
                      let uu___5 =
                        binders_of_list
                          [(a1, true); (t1, true); (t2, true); (f, false)] in
                      FStarC_Compiler_List.op_At uu___4 uu___5 in
                    FStarC_Syntax_Util.abs uu___3 body ret in
                  let c_push1 =
                    let uu___3 = mk_lid "push" in register env2 uu___3 c_push in
                  let ret_tot_wp_a =
                    FStar_Pervasives_Native.Some
                      (FStarC_Syntax_Util.residual_tot wp_a1) in
                  let mk_generic_app c =
                    if (FStarC_Compiler_List.length binders) > Prims.int_zero
                    then
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = args_of_binders binders in
                          {
                            FStarC_Syntax_Syntax.hd = c;
                            FStarC_Syntax_Syntax.args = uu___5
                          } in
                        FStarC_Syntax_Syntax.Tm_app uu___4 in
                      mk uu___3
                    else c in
                  let wp_if_then_else =
                    let result_comp =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.null_binder wp_a1 in
                          let uu___6 =
                            let uu___7 =
                              FStarC_Syntax_Syntax.null_binder wp_a1 in
                            [uu___7] in
                          uu___5 :: uu___6 in
                        let uu___5 = FStarC_Syntax_Syntax.mk_Total wp_a1 in
                        FStarC_Syntax_Util.arrow uu___4 uu___5 in
                      FStarC_Syntax_Syntax.mk_Total uu___3 in
                    let c =
                      FStarC_Syntax_Syntax.gen_bv "c"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let uu___3 =
                      let uu___4 =
                        FStarC_Syntax_Syntax.binders_of_list [a1; c] in
                      FStarC_Compiler_List.op_At binders uu___4 in
                    let uu___4 =
                      let l_ite =
                        FStarC_Syntax_Syntax.fvar_with_dd
                          FStarC_Parser_Const.ite_lid
                          FStar_Pervasives_Native.None in
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStarC_Syntax_Syntax.bv_to_name c in
                                  FStarC_Syntax_Syntax.as_arg uu___11 in
                                [uu___10] in
                              FStarC_Syntax_Util.mk_app l_ite uu___9 in
                            [uu___8] in
                          FStarC_Compiler_List.map
                            FStarC_Syntax_Syntax.as_arg uu___7 in
                        FStarC_Syntax_Util.mk_app c_lift21 uu___6 in
                      FStarC_Syntax_Util.ascribe uu___5
                        ((FStar_Pervasives.Inr result_comp),
                          FStar_Pervasives_Native.None, false) in
                    let uu___5 =
                      let uu___6 =
                        FStarC_Syntax_Util.residual_comp_of_comp result_comp in
                      FStar_Pervasives_Native.Some uu___6 in
                    FStarC_Syntax_Util.abs uu___3 uu___4 uu___5 in
                  let wp_if_then_else1 =
                    let uu___3 = mk_lid "wp_if_then_else" in
                    register env2 uu___3 wp_if_then_else in
                  let wp_if_then_else2 = mk_generic_app wp_if_then_else1 in
                  let wp_close =
                    let b =
                      FStarC_Syntax_Syntax.gen_bv "b"
                        FStar_Pervasives_Native.None FStarC_Syntax_Util.ktype in
                    let t_f =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name b in
                          FStarC_Syntax_Syntax.null_binder uu___5 in
                        [uu___4] in
                      let uu___4 = FStarC_Syntax_Syntax.mk_Total wp_a1 in
                      FStarC_Syntax_Util.arrow uu___3 uu___4 in
                    let f =
                      FStarC_Syntax_Syntax.gen_bv "f"
                        FStar_Pervasives_Native.None t_f in
                    let body =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStarC_Compiler_List.map
                                FStarC_Syntax_Syntax.as_arg
                                [FStarC_Syntax_Util.tforall] in
                            FStarC_Syntax_Util.mk_app c_pure1 uu___6 in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    FStarC_Syntax_Syntax.bv_to_name f in
                                  [uu___10] in
                                FStarC_Compiler_List.map
                                  FStarC_Syntax_Syntax.as_arg uu___9 in
                              FStarC_Syntax_Util.mk_app c_push1 uu___8 in
                            [uu___7] in
                          uu___5 :: uu___6 in
                        FStarC_Compiler_List.map FStarC_Syntax_Syntax.as_arg
                          uu___4 in
                      FStarC_Syntax_Util.mk_app c_app1 uu___3 in
                    let uu___3 =
                      let uu___4 =
                        FStarC_Syntax_Syntax.binders_of_list [a1; b; f] in
                      FStarC_Compiler_List.op_At binders uu___4 in
                    FStarC_Syntax_Util.abs uu___3 body ret_tot_wp_a in
                  let wp_close1 =
                    let uu___3 = mk_lid "wp_close" in
                    register env2 uu___3 wp_close in
                  let wp_close2 = mk_generic_app wp_close1 in
                  let ret_tot_type =
                    FStar_Pervasives_Native.Some
                      (FStarC_Syntax_Util.residual_tot
                         FStarC_Syntax_Util.ktype) in
                  let ret_gtot_type =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          FStarC_Syntax_Syntax.mk_GTotal
                            FStarC_Syntax_Util.ktype in
                        FStarC_TypeChecker_Common.lcomp_of_comp uu___5 in
                      FStarC_TypeChecker_Common.residual_comp_of_lcomp uu___4 in
                    FStar_Pervasives_Native.Some uu___3 in
                  let mk_forall x body =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 = FStarC_Syntax_Syntax.mk_binder x in
                                [uu___9] in
                              FStarC_Syntax_Util.abs uu___8 body ret_tot_type in
                            FStarC_Syntax_Syntax.as_arg uu___7 in
                          [uu___6] in
                        {
                          FStarC_Syntax_Syntax.hd =
                            FStarC_Syntax_Util.tforall;
                          FStarC_Syntax_Syntax.args = uu___5
                        } in
                      FStarC_Syntax_Syntax.Tm_app uu___4 in
                    FStarC_Syntax_Syntax.mk uu___3
                      FStarC_Compiler_Range_Type.dummyRange in
                  let rec is_discrete t =
                    let uu___3 =
                      let uu___4 = FStarC_Syntax_Subst.compress t in
                      uu___4.FStarC_Syntax_Syntax.n in
                    match uu___3 with
                    | FStarC_Syntax_Syntax.Tm_type uu___4 -> false
                    | FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = bs;
                          FStarC_Syntax_Syntax.comp = c;_}
                        ->
                        (FStarC_Compiler_List.for_all
                           (fun uu___4 ->
                              match uu___4 with
                              | { FStarC_Syntax_Syntax.binder_bv = b;
                                  FStarC_Syntax_Syntax.binder_qual = uu___5;
                                  FStarC_Syntax_Syntax.binder_positivity =
                                    uu___6;
                                  FStarC_Syntax_Syntax.binder_attrs = uu___7;_}
                                  -> is_discrete b.FStarC_Syntax_Syntax.sort)
                           bs)
                          && (is_discrete (FStarC_Syntax_Util.comp_result c))
                    | uu___4 -> true in
                  let rec is_monotonic t =
                    let uu___3 =
                      let uu___4 = FStarC_Syntax_Subst.compress t in
                      uu___4.FStarC_Syntax_Syntax.n in
                    match uu___3 with
                    | FStarC_Syntax_Syntax.Tm_type uu___4 -> true
                    | FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = bs;
                          FStarC_Syntax_Syntax.comp = c;_}
                        ->
                        (FStarC_Compiler_List.for_all
                           (fun uu___4 ->
                              match uu___4 with
                              | { FStarC_Syntax_Syntax.binder_bv = b;
                                  FStarC_Syntax_Syntax.binder_qual = uu___5;
                                  FStarC_Syntax_Syntax.binder_positivity =
                                    uu___6;
                                  FStarC_Syntax_Syntax.binder_attrs = uu___7;_}
                                  -> is_discrete b.FStarC_Syntax_Syntax.sort)
                           bs)
                          &&
                          (is_monotonic (FStarC_Syntax_Util.comp_result c))
                    | uu___4 -> is_discrete t in
                  let rec mk_rel rel t x y =
                    let mk_rel1 = mk_rel rel in
                    let t1 =
                      FStarC_TypeChecker_Normalize.normalize
                        [FStarC_TypeChecker_Env.Beta;
                        FStarC_TypeChecker_Env.Eager_unfolding;
                        FStarC_TypeChecker_Env.DontUnfoldAttr
                          [FStarC_Parser_Const.tac_opaque_attr];
                        FStarC_TypeChecker_Env.UnfoldUntil
                          FStarC_Syntax_Syntax.delta_constant] env2 t in
                    let uu___3 =
                      let uu___4 = FStarC_Syntax_Subst.compress t1 in
                      uu___4.FStarC_Syntax_Syntax.n in
                    match uu___3 with
                    | FStarC_Syntax_Syntax.Tm_type uu___4 -> rel x y
                    | FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = binder::[];
                          FStarC_Syntax_Syntax.comp =
                            {
                              FStarC_Syntax_Syntax.n =
                                FStarC_Syntax_Syntax.GTotal b;
                              FStarC_Syntax_Syntax.pos = uu___4;
                              FStarC_Syntax_Syntax.vars = uu___5;
                              FStarC_Syntax_Syntax.hash_code = uu___6;_};_}
                        ->
                        let a2 =
                          (binder.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                        let uu___7 = (is_monotonic a2) || (is_monotonic b) in
                        if uu___7
                        then
                          let a11 =
                            FStarC_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStarC_Syntax_Syntax.bv_to_name a11 in
                                  FStarC_Syntax_Syntax.as_arg uu___11 in
                                [uu___10] in
                              FStarC_Syntax_Util.mk_app x uu___9 in
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStarC_Syntax_Syntax.bv_to_name a11 in
                                  FStarC_Syntax_Syntax.as_arg uu___12 in
                                [uu___11] in
                              FStarC_Syntax_Util.mk_app y uu___10 in
                            mk_rel1 b uu___8 uu___9 in
                          mk_forall a11 body
                        else
                          (let a11 =
                             FStarC_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStarC_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu___9 =
                               let uu___10 =
                                 FStarC_Syntax_Syntax.bv_to_name a11 in
                               let uu___11 =
                                 FStarC_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu___10 uu___11 in
                             let uu___10 =
                               let uu___11 =
                                 let uu___12 =
                                   let uu___13 =
                                     let uu___14 =
                                       FStarC_Syntax_Syntax.bv_to_name a11 in
                                     FStarC_Syntax_Syntax.as_arg uu___14 in
                                   [uu___13] in
                                 FStarC_Syntax_Util.mk_app x uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   let uu___14 =
                                     let uu___15 =
                                       FStarC_Syntax_Syntax.bv_to_name a21 in
                                     FStarC_Syntax_Syntax.as_arg uu___15 in
                                   [uu___14] in
                                 FStarC_Syntax_Util.mk_app y uu___13 in
                               mk_rel1 b uu___11 uu___12 in
                             FStarC_Syntax_Util.mk_imp uu___9 uu___10 in
                           let uu___9 = mk_forall a21 body in
                           mk_forall a11 uu___9)
                    | FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = binder::[];
                          FStarC_Syntax_Syntax.comp =
                            {
                              FStarC_Syntax_Syntax.n =
                                FStarC_Syntax_Syntax.Total b;
                              FStarC_Syntax_Syntax.pos = uu___4;
                              FStarC_Syntax_Syntax.vars = uu___5;
                              FStarC_Syntax_Syntax.hash_code = uu___6;_};_}
                        ->
                        let a2 =
                          (binder.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                        let uu___7 = (is_monotonic a2) || (is_monotonic b) in
                        if uu___7
                        then
                          let a11 =
                            FStarC_Syntax_Syntax.gen_bv "a1"
                              FStar_Pervasives_Native.None a2 in
                          let body =
                            let uu___8 =
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStarC_Syntax_Syntax.bv_to_name a11 in
                                  FStarC_Syntax_Syntax.as_arg uu___11 in
                                [uu___10] in
                              FStarC_Syntax_Util.mk_app x uu___9 in
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  let uu___12 =
                                    FStarC_Syntax_Syntax.bv_to_name a11 in
                                  FStarC_Syntax_Syntax.as_arg uu___12 in
                                [uu___11] in
                              FStarC_Syntax_Util.mk_app y uu___10 in
                            mk_rel1 b uu___8 uu___9 in
                          mk_forall a11 body
                        else
                          (let a11 =
                             FStarC_Syntax_Syntax.gen_bv "a1"
                               FStar_Pervasives_Native.None a2 in
                           let a21 =
                             FStarC_Syntax_Syntax.gen_bv "a2"
                               FStar_Pervasives_Native.None a2 in
                           let body =
                             let uu___9 =
                               let uu___10 =
                                 FStarC_Syntax_Syntax.bv_to_name a11 in
                               let uu___11 =
                                 FStarC_Syntax_Syntax.bv_to_name a21 in
                               mk_rel1 a2 uu___10 uu___11 in
                             let uu___10 =
                               let uu___11 =
                                 let uu___12 =
                                   let uu___13 =
                                     let uu___14 =
                                       FStarC_Syntax_Syntax.bv_to_name a11 in
                                     FStarC_Syntax_Syntax.as_arg uu___14 in
                                   [uu___13] in
                                 FStarC_Syntax_Util.mk_app x uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   let uu___14 =
                                     let uu___15 =
                                       FStarC_Syntax_Syntax.bv_to_name a21 in
                                     FStarC_Syntax_Syntax.as_arg uu___15 in
                                   [uu___14] in
                                 FStarC_Syntax_Util.mk_app y uu___13 in
                               mk_rel1 b uu___11 uu___12 in
                             FStarC_Syntax_Util.mk_imp uu___9 uu___10 in
                           let uu___9 = mk_forall a21 body in
                           mk_forall a11 uu___9)
                    | FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = binder::binders1;
                          FStarC_Syntax_Syntax.comp = comp;_}
                        ->
                        let t2 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStarC_Syntax_Util.arrow binders1 comp in
                                FStarC_Syntax_Syntax.mk_Total uu___7 in
                              {
                                FStarC_Syntax_Syntax.bs1 = [binder];
                                FStarC_Syntax_Syntax.comp = uu___6
                              } in
                            FStarC_Syntax_Syntax.Tm_arrow uu___5 in
                          {
                            FStarC_Syntax_Syntax.n = uu___4;
                            FStarC_Syntax_Syntax.pos =
                              (t1.FStarC_Syntax_Syntax.pos);
                            FStarC_Syntax_Syntax.vars =
                              (t1.FStarC_Syntax_Syntax.vars);
                            FStarC_Syntax_Syntax.hash_code =
                              (t1.FStarC_Syntax_Syntax.hash_code)
                          } in
                        mk_rel1 t2 x y
                    | FStarC_Syntax_Syntax.Tm_arrow
                        { FStarC_Syntax_Syntax.bs1 = [];
                          FStarC_Syntax_Syntax.comp = uu___4;_}
                        -> failwith "impossible: arrow with empty binders"
                    | uu___4 -> FStarC_Syntax_Util.mk_untyped_eq2 x y in
                  let stronger =
                    let wp1 =
                      FStarC_Syntax_Syntax.gen_bv "wp1"
                        FStar_Pervasives_Native.None wp_a1 in
                    let wp2 =
                      FStarC_Syntax_Syntax.gen_bv "wp2"
                        FStar_Pervasives_Native.None wp_a1 in
                    let rec mk_stronger t x y =
                      let t1 =
                        FStarC_TypeChecker_Normalize.normalize
                          [FStarC_TypeChecker_Env.Beta;
                          FStarC_TypeChecker_Env.Eager_unfolding;
                          FStarC_TypeChecker_Env.DontUnfoldAttr
                            [FStarC_Parser_Const.tac_opaque_attr];
                          FStarC_TypeChecker_Env.UnfoldUntil
                            FStarC_Syntax_Syntax.delta_constant] env2 t in
                      let uu___3 =
                        let uu___4 = FStarC_Syntax_Subst.compress t1 in
                        uu___4.FStarC_Syntax_Syntax.n in
                      match uu___3 with
                      | FStarC_Syntax_Syntax.Tm_type uu___4 ->
                          FStarC_Syntax_Util.mk_imp x y
                      | FStarC_Syntax_Syntax.Tm_app
                          { FStarC_Syntax_Syntax.hd = head;
                            FStarC_Syntax_Syntax.args = args;_}
                          when
                          let uu___4 = FStarC_Syntax_Subst.compress head in
                          FStarC_Syntax_Util.is_tuple_constructor uu___4 ->
                          let project i tuple =
                            let projector =
                              let uu___4 =
                                let uu___5 =
                                  FStarC_Parser_Const.mk_tuple_data_lid
                                    (FStarC_Compiler_List.length args)
                                    FStarC_Compiler_Range_Type.dummyRange in
                                FStarC_TypeChecker_Env.lookup_projector env2
                                  uu___5 i in
                              FStarC_Syntax_Syntax.fvar_with_dd uu___4
                                FStar_Pervasives_Native.None in
                            FStarC_Syntax_Util.mk_app projector
                              [(tuple, FStar_Pervasives_Native.None)] in
                          let uu___4 =
                            let uu___5 =
                              FStarC_Compiler_List.mapi
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
                               FStarC_Compiler_List.fold_left
                                 FStarC_Syntax_Util.mk_conj rel0 rels)
                      | FStarC_Syntax_Syntax.Tm_arrow
                          { FStarC_Syntax_Syntax.bs1 = binders1;
                            FStarC_Syntax_Syntax.comp =
                              {
                                FStarC_Syntax_Syntax.n =
                                  FStarC_Syntax_Syntax.GTotal b;
                                FStarC_Syntax_Syntax.pos = uu___4;
                                FStarC_Syntax_Syntax.vars = uu___5;
                                FStarC_Syntax_Syntax.hash_code = uu___6;_};_}
                          ->
                          let bvs =
                            FStarC_Compiler_List.mapi
                              (fun i ->
                                 fun uu___7 ->
                                   match uu___7 with
                                   | { FStarC_Syntax_Syntax.binder_bv = bv;
                                       FStarC_Syntax_Syntax.binder_qual = q;
                                       FStarC_Syntax_Syntax.binder_positivity
                                         = uu___8;
                                       FStarC_Syntax_Syntax.binder_attrs =
                                         uu___9;_}
                                       ->
                                       let uu___10 =
                                         let uu___11 =
                                           FStarC_Compiler_Util.string_of_int
                                             i in
                                         Prims.strcat "a" uu___11 in
                                       FStarC_Syntax_Syntax.gen_bv uu___10
                                         FStar_Pervasives_Native.None
                                         bv.FStarC_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStarC_Compiler_List.map
                              (fun ai ->
                                 let uu___7 =
                                   FStarC_Syntax_Syntax.bv_to_name ai in
                                 FStarC_Syntax_Syntax.as_arg uu___7) bvs in
                          let body =
                            let uu___7 = FStarC_Syntax_Util.mk_app x args in
                            let uu___8 = FStarC_Syntax_Util.mk_app y args in
                            mk_stronger b uu___7 uu___8 in
                          FStarC_Compiler_List.fold_right
                            (fun bv -> fun body1 -> mk_forall bv body1) bvs
                            body
                      | FStarC_Syntax_Syntax.Tm_arrow
                          { FStarC_Syntax_Syntax.bs1 = binders1;
                            FStarC_Syntax_Syntax.comp =
                              {
                                FStarC_Syntax_Syntax.n =
                                  FStarC_Syntax_Syntax.Total b;
                                FStarC_Syntax_Syntax.pos = uu___4;
                                FStarC_Syntax_Syntax.vars = uu___5;
                                FStarC_Syntax_Syntax.hash_code = uu___6;_};_}
                          ->
                          let bvs =
                            FStarC_Compiler_List.mapi
                              (fun i ->
                                 fun uu___7 ->
                                   match uu___7 with
                                   | { FStarC_Syntax_Syntax.binder_bv = bv;
                                       FStarC_Syntax_Syntax.binder_qual = q;
                                       FStarC_Syntax_Syntax.binder_positivity
                                         = uu___8;
                                       FStarC_Syntax_Syntax.binder_attrs =
                                         uu___9;_}
                                       ->
                                       let uu___10 =
                                         let uu___11 =
                                           FStarC_Compiler_Util.string_of_int
                                             i in
                                         Prims.strcat "a" uu___11 in
                                       FStarC_Syntax_Syntax.gen_bv uu___10
                                         FStar_Pervasives_Native.None
                                         bv.FStarC_Syntax_Syntax.sort)
                              binders1 in
                          let args =
                            FStarC_Compiler_List.map
                              (fun ai ->
                                 let uu___7 =
                                   FStarC_Syntax_Syntax.bv_to_name ai in
                                 FStarC_Syntax_Syntax.as_arg uu___7) bvs in
                          let body =
                            let uu___7 = FStarC_Syntax_Util.mk_app x args in
                            let uu___8 = FStarC_Syntax_Util.mk_app y args in
                            mk_stronger b uu___7 uu___8 in
                          FStarC_Compiler_List.fold_right
                            (fun bv -> fun body1 -> mk_forall bv body1) bvs
                            body
                      | uu___4 -> failwith "Not a DM elaborated type" in
                    let body =
                      let uu___3 = FStarC_Syntax_Util.unascribe wp_a1 in
                      let uu___4 = FStarC_Syntax_Syntax.bv_to_name wp1 in
                      let uu___5 = FStarC_Syntax_Syntax.bv_to_name wp2 in
                      mk_stronger uu___3 uu___4 uu___5 in
                    let uu___3 =
                      let uu___4 =
                        binders_of_list
                          [(a1, false); (wp1, false); (wp2, false)] in
                      FStarC_Compiler_List.op_At binders uu___4 in
                    FStarC_Syntax_Util.abs uu___3 body ret_tot_type in
                  let stronger1 =
                    let uu___3 = mk_lid "stronger" in
                    register env2 uu___3 stronger in
                  let stronger2 = mk_generic_app stronger1 in
                  let ite_wp =
                    let wp =
                      FStarC_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu___3 = FStarC_Compiler_Util.prefix gamma in
                    match uu___3 with
                    | (wp_args, post) ->
                        let k =
                          FStarC_Syntax_Syntax.gen_bv "k"
                            FStar_Pervasives_Native.None
                            (post.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                        let equiv =
                          let k_tm = FStarC_Syntax_Syntax.bv_to_name k in
                          let eq =
                            let uu___4 =
                              FStarC_Syntax_Syntax.bv_to_name
                                post.FStarC_Syntax_Syntax.binder_bv in
                            mk_rel FStarC_Syntax_Util.mk_iff
                              k.FStarC_Syntax_Syntax.sort k_tm uu___4 in
                          let uu___4 =
                            FStarC_Syntax_Formula.destruct_typ_as_formula eq in
                          match uu___4 with
                          | FStar_Pervasives_Native.Some
                              (FStarC_Syntax_Formula.QAll
                              (binders1, [], body)) ->
                              let k_app =
                                let uu___5 = args_of_binders binders1 in
                                FStarC_Syntax_Util.mk_app k_tm uu___5 in
                              let guard_free =
                                let uu___5 =
                                  FStarC_Syntax_Syntax.lid_and_dd_as_fv
                                    FStarC_Parser_Const.guard_free
                                    FStar_Pervasives_Native.None in
                                FStarC_Syntax_Syntax.fv_to_tm uu___5 in
                              let pat =
                                let uu___5 =
                                  let uu___6 =
                                    FStarC_Syntax_Syntax.as_arg k_app in
                                  [uu___6] in
                                FStarC_Syntax_Util.mk_app guard_free uu___5 in
                              let pattern_guarded_body =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 =
                                      let uu___8 =
                                        let uu___9 =
                                          FStarC_Syntax_Syntax.binders_to_names
                                            binders1 in
                                        let uu___10 =
                                          let uu___11 =
                                            let uu___12 =
                                              FStarC_Syntax_Syntax.as_arg pat in
                                            [uu___12] in
                                          [uu___11] in
                                        (uu___9, uu___10) in
                                      FStarC_Syntax_Syntax.Meta_pattern
                                        uu___8 in
                                    {
                                      FStarC_Syntax_Syntax.tm2 = body;
                                      FStarC_Syntax_Syntax.meta = uu___7
                                    } in
                                  FStarC_Syntax_Syntax.Tm_meta uu___6 in
                                mk uu___5 in
                              FStarC_Syntax_Util.close_forall_no_univs
                                binders1 pattern_guarded_body
                          | uu___5 ->
                              failwith
                                "Impossible: Expected the equivalence to be a quantified formula" in
                        let body =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStarC_Syntax_Syntax.bv_to_name wp in
                                let uu___8 =
                                  let uu___9 = args_of_binders wp_args in
                                  let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        FStarC_Syntax_Syntax.bv_to_name k in
                                      FStarC_Syntax_Syntax.as_arg uu___12 in
                                    [uu___11] in
                                  FStarC_Compiler_List.op_At uu___9 uu___10 in
                                FStarC_Syntax_Util.mk_app uu___7 uu___8 in
                              FStarC_Syntax_Util.mk_imp equiv uu___6 in
                            FStarC_Syntax_Util.mk_forall_no_univ k uu___5 in
                          FStarC_Syntax_Util.abs gamma uu___4 ret_gtot_type in
                        let uu___4 =
                          let uu___5 =
                            FStarC_Syntax_Syntax.binders_of_list [a1; wp] in
                          FStarC_Compiler_List.op_At binders uu___5 in
                        FStarC_Syntax_Util.abs uu___4 body ret_gtot_type in
                  let ite_wp1 =
                    let uu___3 = mk_lid "ite_wp" in
                    register env2 uu___3 ite_wp in
                  let ite_wp2 = mk_generic_app ite_wp1 in
                  let null_wp =
                    let wp =
                      FStarC_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let uu___3 = FStarC_Compiler_Util.prefix gamma in
                    match uu___3 with
                    | (wp_args, post) ->
                        let x =
                          FStarC_Syntax_Syntax.gen_bv "x"
                            FStar_Pervasives_Native.None
                            FStarC_Syntax_Syntax.tun in
                        let body =
                          let uu___4 =
                            let uu___5 =
                              FStarC_Syntax_Syntax.bv_to_name
                                post.FStarC_Syntax_Syntax.binder_bv in
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  FStarC_Syntax_Syntax.bv_to_name x in
                                FStarC_Syntax_Syntax.as_arg uu___8 in
                              [uu___7] in
                            FStarC_Syntax_Util.mk_app uu___5 uu___6 in
                          FStarC_Syntax_Util.mk_forall_no_univ x uu___4 in
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStarC_Syntax_Syntax.binders_of_list [a1] in
                            FStarC_Compiler_List.op_At uu___6 gamma in
                          FStarC_Compiler_List.op_At binders uu___5 in
                        FStarC_Syntax_Util.abs uu___4 body ret_gtot_type in
                  let null_wp1 =
                    let uu___3 = mk_lid "null_wp" in
                    register env2 uu___3 null_wp in
                  let null_wp2 = mk_generic_app null_wp1 in
                  let wp_trivial =
                    let wp =
                      FStarC_Syntax_Syntax.gen_bv "wp"
                        FStar_Pervasives_Native.None wp_a1 in
                    let body =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_Syntax_Syntax.bv_to_name a1 in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    FStarC_Syntax_Syntax.bv_to_name a1 in
                                  FStarC_Syntax_Syntax.as_arg uu___10 in
                                [uu___9] in
                              FStarC_Syntax_Util.mk_app null_wp2 uu___8 in
                            let uu___8 =
                              let uu___9 = FStarC_Syntax_Syntax.bv_to_name wp in
                              [uu___9] in
                            uu___7 :: uu___8 in
                          uu___5 :: uu___6 in
                        FStarC_Compiler_List.map FStarC_Syntax_Syntax.as_arg
                          uu___4 in
                      FStarC_Syntax_Util.mk_app stronger2 uu___3 in
                    let uu___3 =
                      let uu___4 =
                        FStarC_Syntax_Syntax.binders_of_list [a1; wp] in
                      FStarC_Compiler_List.op_At binders uu___4 in
                    FStarC_Syntax_Util.abs uu___3 body ret_tot_type in
                  let wp_trivial1 =
                    let uu___3 = mk_lid "wp_trivial" in
                    register env2 uu___3 wp_trivial in
                  let wp_trivial2 = mk_generic_app wp_trivial1 in
                  ((let uu___4 = FStarC_Compiler_Effect.op_Bang dbg in
                    if uu___4 then d1 "End Dijkstra monads for free" else ());
                   (let c = FStarC_Syntax_Subst.close binders in
                    let ed_combs =
                      match ed.FStarC_Syntax_Syntax.combinators with
                      | FStarC_Syntax_Syntax.DM4F_eff combs ->
                          let uu___4 =
                            let uu___5 =
                              let uu___6 = c stronger2 in ([], uu___6) in
                            let uu___6 =
                              let uu___7 = c wp_if_then_else2 in ([], uu___7) in
                            let uu___7 =
                              let uu___8 = c ite_wp2 in ([], uu___8) in
                            let uu___8 =
                              let uu___9 = c wp_close2 in ([], uu___9) in
                            let uu___9 =
                              let uu___10 = c wp_trivial2 in ([], uu___10) in
                            {
                              FStarC_Syntax_Syntax.ret_wp =
                                (combs.FStarC_Syntax_Syntax.ret_wp);
                              FStarC_Syntax_Syntax.bind_wp =
                                (combs.FStarC_Syntax_Syntax.bind_wp);
                              FStarC_Syntax_Syntax.stronger = uu___5;
                              FStarC_Syntax_Syntax.if_then_else = uu___6;
                              FStarC_Syntax_Syntax.ite_wp = uu___7;
                              FStarC_Syntax_Syntax.close_wp = uu___8;
                              FStarC_Syntax_Syntax.trivial = uu___9;
                              FStarC_Syntax_Syntax.repr =
                                (combs.FStarC_Syntax_Syntax.repr);
                              FStarC_Syntax_Syntax.return_repr =
                                (combs.FStarC_Syntax_Syntax.return_repr);
                              FStarC_Syntax_Syntax.bind_repr =
                                (combs.FStarC_Syntax_Syntax.bind_repr)
                            } in
                          FStarC_Syntax_Syntax.DM4F_eff uu___4
                      | uu___4 ->
                          failwith
                            "Impossible! For a DM4F effect combinators must be in DM4f_eff" in
                    let uu___4 =
                      let uu___5 = FStarC_Compiler_Effect.op_Bang sigelts in
                      FStarC_Compiler_List.rev uu___5 in
                    (uu___4,
                      {
                        FStarC_Syntax_Syntax.mname =
                          (ed.FStarC_Syntax_Syntax.mname);
                        FStarC_Syntax_Syntax.cattributes =
                          (ed.FStarC_Syntax_Syntax.cattributes);
                        FStarC_Syntax_Syntax.univs =
                          (ed.FStarC_Syntax_Syntax.univs);
                        FStarC_Syntax_Syntax.binders =
                          (ed.FStarC_Syntax_Syntax.binders);
                        FStarC_Syntax_Syntax.signature =
                          (ed.FStarC_Syntax_Syntax.signature);
                        FStarC_Syntax_Syntax.combinators = ed_combs;
                        FStarC_Syntax_Syntax.actions =
                          (ed.FStarC_Syntax_Syntax.actions);
                        FStarC_Syntax_Syntax.eff_attrs =
                          (ed.FStarC_Syntax_Syntax.eff_attrs);
                        FStarC_Syntax_Syntax.extraction_mode =
                          (ed.FStarC_Syntax_Syntax.extraction_mode)
                      })))))
type env_ = env
let (get_env : env -> FStarC_TypeChecker_Env.env) = fun env1 -> env1.tcenv
let (set_env : env -> FStarC_TypeChecker_Env.env -> env) =
  fun dmff_env ->
    fun env' ->
      {
        tcenv = env';
        subst = (dmff_env.subst);
        tc_const = (dmff_env.tc_const)
      }
type nm =
  | N of FStarC_Syntax_Syntax.typ 
  | M of FStarC_Syntax_Syntax.typ 
let (uu___is_N : nm -> Prims.bool) =
  fun projectee -> match projectee with | N _0 -> true | uu___ -> false
let (__proj__N__item___0 : nm -> FStarC_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | N _0 -> _0
let (uu___is_M : nm -> Prims.bool) =
  fun projectee -> match projectee with | M _0 -> true | uu___ -> false
let (__proj__M__item___0 : nm -> FStarC_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | M _0 -> _0
type nm_ = nm
let (nm_of_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> nm) =
  fun c ->
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total t -> N t
    | FStarC_Syntax_Syntax.Comp c1 when
        FStarC_Compiler_Util.for_some
          (fun uu___ ->
             match uu___ with
             | FStarC_Syntax_Syntax.CPS -> true
             | uu___1 -> false) c1.FStarC_Syntax_Syntax.flags
        -> M (c1.FStarC_Syntax_Syntax.result_typ)
    | uu___ ->
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c in
          FStarC_Compiler_Util.format1
            "[nm_of_comp]: unexpected computation type %s" uu___2 in
        FStarC_Errors.raise_error (FStarC_Syntax_Syntax.has_range_syntax ())
          c FStarC_Errors_Codes.Error_UnexpectedDM4FType ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic uu___1)
let (string_of_nm : nm -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | N t ->
        let uu___1 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
        FStarC_Compiler_Util.format1 "N[%s]" uu___1
    | M t ->
        let uu___1 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
        FStarC_Compiler_Util.format1 "M[%s]" uu___1
let (is_monadic_arrow : FStarC_Syntax_Syntax.term' -> nm) =
  fun n ->
    match n with
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = uu___; FStarC_Syntax_Syntax.comp = c;_}
        -> nm_of_comp c
    | uu___ -> failwith "unexpected_argument: [is_monadic_arrow]"
let (is_monadic_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    let uu___ = nm_of_comp c in
    match uu___ with | M uu___1 -> true | N uu___1 -> false
exception Not_found 
let (uu___is_Not_found : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Not_found -> true | uu___ -> false
let (double_star : FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ) =
  fun typ ->
    let star_once typ1 =
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ1 in
          FStarC_Syntax_Syntax.mk_binder uu___2 in
        [uu___1] in
      let uu___1 = FStarC_Syntax_Syntax.mk_Total FStarC_Syntax_Util.ktype0 in
      FStarC_Syntax_Util.arrow uu___ uu___1 in
    let uu___ = star_once typ in star_once uu___
let rec (mk_star_to_type :
  (FStarC_Syntax_Syntax.term' ->
     FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
    ->
    env ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
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
                  FStarC_Syntax_Syntax.null_bv uu___5 in
                let uu___5 = FStarC_Syntax_Syntax.as_bqual_implicit false in
                FStarC_Syntax_Syntax.mk_binder_with_attrs uu___4 uu___5
                  FStar_Pervasives_Native.None [] in
              [uu___3] in
            let uu___3 =
              FStarC_Syntax_Syntax.mk_Total FStarC_Syntax_Util.ktype0 in
            {
              FStarC_Syntax_Syntax.bs1 = uu___2;
              FStarC_Syntax_Syntax.comp = uu___3
            } in
          FStarC_Syntax_Syntax.Tm_arrow uu___1 in
        mk uu___
and (star_type' :
  env ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term)
  =
  fun env1 ->
    fun t ->
      let mk x = FStarC_Syntax_Syntax.mk x t.FStarC_Syntax_Syntax.pos in
      let mk_star_to_type1 = mk_star_to_type mk in
      let t1 = FStarC_Syntax_Subst.compress t in
      match t1.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Tm_arrow
          { FStarC_Syntax_Syntax.bs1 = binders;
            FStarC_Syntax_Syntax.comp = uu___;_}
          ->
          let binders1 =
            FStarC_Compiler_List.map
              (fun b ->
                 let uu___1 =
                   let uu___2 = b.FStarC_Syntax_Syntax.binder_bv in
                   let uu___3 =
                     star_type' env1
                       (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                   {
                     FStarC_Syntax_Syntax.ppname =
                       (uu___2.FStarC_Syntax_Syntax.ppname);
                     FStarC_Syntax_Syntax.index =
                       (uu___2.FStarC_Syntax_Syntax.index);
                     FStarC_Syntax_Syntax.sort = uu___3
                   } in
                 {
                   FStarC_Syntax_Syntax.binder_bv = uu___1;
                   FStarC_Syntax_Syntax.binder_qual =
                     (b.FStarC_Syntax_Syntax.binder_qual);
                   FStarC_Syntax_Syntax.binder_positivity =
                     (b.FStarC_Syntax_Syntax.binder_positivity);
                   FStarC_Syntax_Syntax.binder_attrs =
                     (b.FStarC_Syntax_Syntax.binder_attrs)
                 }) binders in
          (match t1.FStarC_Syntax_Syntax.n with
           | FStarC_Syntax_Syntax.Tm_arrow
               { FStarC_Syntax_Syntax.bs1 = uu___1;
                 FStarC_Syntax_Syntax.comp =
                   { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.GTotal hn;
                     FStarC_Syntax_Syntax.pos = uu___2;
                     FStarC_Syntax_Syntax.vars = uu___3;
                     FStarC_Syntax_Syntax.hash_code = uu___4;_};_}
               ->
               let uu___5 =
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = star_type' env1 hn in
                     FStarC_Syntax_Syntax.mk_GTotal uu___8 in
                   {
                     FStarC_Syntax_Syntax.bs1 = binders1;
                     FStarC_Syntax_Syntax.comp = uu___7
                   } in
                 FStarC_Syntax_Syntax.Tm_arrow uu___6 in
               mk uu___5
           | uu___1 ->
               let uu___2 = is_monadic_arrow t1.FStarC_Syntax_Syntax.n in
               (match uu___2 with
                | N hn ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = star_type' env1 hn in
                          FStarC_Syntax_Syntax.mk_Total uu___6 in
                        {
                          FStarC_Syntax_Syntax.bs1 = binders1;
                          FStarC_Syntax_Syntax.comp = uu___5
                        } in
                      FStarC_Syntax_Syntax.Tm_arrow uu___4 in
                    mk uu___3
                | M a ->
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                let uu___9 = mk_star_to_type1 env1 a in
                                FStarC_Syntax_Syntax.null_bv uu___9 in
                              let uu___9 =
                                FStarC_Syntax_Syntax.as_bqual_implicit false in
                              FStarC_Syntax_Syntax.mk_binder_with_attrs
                                uu___8 uu___9 FStar_Pervasives_Native.None [] in
                            [uu___7] in
                          FStarC_Compiler_List.op_At binders1 uu___6 in
                        let uu___6 =
                          FStarC_Syntax_Syntax.mk_Total
                            FStarC_Syntax_Util.ktype0 in
                        {
                          FStarC_Syntax_Syntax.bs1 = uu___5;
                          FStarC_Syntax_Syntax.comp = uu___6
                        } in
                      FStarC_Syntax_Syntax.Tm_arrow uu___4 in
                    mk uu___3))
      | FStarC_Syntax_Syntax.Tm_app
          { FStarC_Syntax_Syntax.hd = head;
            FStarC_Syntax_Syntax.args = args;_}
          ->
          let debug t2 s =
            let uu___ =
              let uu___1 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
              let uu___2 =
                FStarC_Class_Show.show
                  (FStarC_Compiler_FlatSet.showable_set
                     FStarC_Syntax_Syntax.ord_bv
                     FStarC_Syntax_Print.showable_bv) s in
              FStarC_Compiler_Util.format2 "Dependency found in term %s : %s"
                uu___1 uu___2 in
            FStarC_Errors.log_issue
              (FStarC_Syntax_Syntax.has_range_syntax ()) t2
              FStarC_Errors_Codes.Warning_DependencyFound ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___) in
          let rec is_non_dependent_arrow ty n =
            let uu___ =
              let uu___1 = FStarC_Syntax_Subst.compress ty in
              uu___1.FStarC_Syntax_Syntax.n in
            match uu___ with
            | FStarC_Syntax_Syntax.Tm_arrow
                { FStarC_Syntax_Syntax.bs1 = binders;
                  FStarC_Syntax_Syntax.comp = c;_}
                ->
                let uu___1 =
                  let uu___2 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
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
                                let uu___4 = FStarC_Syntax_Free.names ty1 in
                                Obj.magic
                                  (FStarC_Class_Setlike.inter ()
                                     (Obj.magic
                                        (FStarC_Compiler_FlatSet.setlike_flat_set
                                           FStarC_Syntax_Syntax.ord_bv))
                                     (Obj.magic uu___4) (Obj.magic s)) in
                              let uu___4 =
                                let uu___5 =
                                  FStarC_Class_Setlike.is_empty ()
                                    (Obj.magic
                                       (FStarC_Compiler_FlatSet.setlike_flat_set
                                          FStarC_Syntax_Syntax.ord_bv))
                                    (Obj.magic sinter) in
                                Prims.op_Negation uu___5 in
                              if uu___4
                              then
                                (debug ty1 sinter;
                                 FStarC_Compiler_Effect.raise Not_found)
                              else () in
                            let uu___4 =
                              FStarC_Syntax_Subst.open_comp binders c in
                            (match uu___4 with
                             | (binders1, c1) ->
                                 let s =
                                   let uu___5 =
                                     Obj.magic
                                       (FStarC_Class_Setlike.empty ()
                                          (Obj.magic
                                             (FStarC_Compiler_FlatSet.setlike_flat_set
                                                FStarC_Syntax_Syntax.ord_bv))
                                          ()) in
                                   FStarC_Compiler_List.fold_left
                                     (fun uu___7 ->
                                        fun uu___6 ->
                                          (fun s1 ->
                                             fun uu___6 ->
                                               match uu___6 with
                                               | {
                                                   FStarC_Syntax_Syntax.binder_bv
                                                     = bv;
                                                   FStarC_Syntax_Syntax.binder_qual
                                                     = uu___7;
                                                   FStarC_Syntax_Syntax.binder_positivity
                                                     = uu___8;
                                                   FStarC_Syntax_Syntax.binder_attrs
                                                     = uu___9;_}
                                                   ->
                                                   (non_dependent_or_raise s1
                                                      bv.FStarC_Syntax_Syntax.sort;
                                                    Obj.magic
                                                      (FStarC_Class_Setlike.add
                                                         ()
                                                         (Obj.magic
                                                            (FStarC_Compiler_FlatSet.setlike_flat_set
                                                               FStarC_Syntax_Syntax.ord_bv))
                                                         bv (Obj.magic s1))))
                                            uu___7 uu___6) uu___5 binders1 in
                                 let ct = FStarC_Syntax_Util.comp_result c1 in
                                 (non_dependent_or_raise s ct;
                                  (let k =
                                     n -
                                       (FStarC_Compiler_List.length binders1) in
                                   if k > Prims.int_zero
                                   then is_non_dependent_arrow ct k
                                   else true)))) ()
                   with | Not_found -> false)
            | uu___1 ->
                ((let uu___3 =
                    let uu___4 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term ty in
                    FStarC_Compiler_Util.format1 "Not a dependent arrow : %s"
                      uu___4 in
                  FStarC_Errors.log_issue
                    (FStarC_Syntax_Syntax.has_range_syntax ()) ty
                    FStarC_Errors_Codes.Warning_NotDependentArrow ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic uu___3));
                 false) in
          let rec is_valid_application head1 =
            let uu___ =
              let uu___1 = FStarC_Syntax_Subst.compress head1 in
              uu___1.FStarC_Syntax_Syntax.n in
            match uu___ with
            | FStarC_Syntax_Syntax.Tm_fvar fv when
                (((FStarC_Syntax_Syntax.fv_eq_lid fv
                     FStarC_Parser_Const.option_lid)
                    ||
                    (FStarC_Syntax_Syntax.fv_eq_lid fv
                       FStarC_Parser_Const.either_lid))
                   ||
                   (FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.eq2_lid))
                  ||
                  (let uu___1 = FStarC_Syntax_Subst.compress head1 in
                   FStarC_Syntax_Util.is_tuple_constructor uu___1)
                -> true
            | FStarC_Syntax_Syntax.Tm_fvar fv ->
                let uu___1 =
                  FStarC_TypeChecker_Env.lookup_lid env1.tcenv
                    (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
                (match uu___1 with
                 | ((uu___2, ty), uu___3) ->
                     let uu___4 =
                       is_non_dependent_arrow ty
                         (FStarC_Compiler_List.length args) in
                     if uu___4
                     then
                       let res =
                         FStarC_TypeChecker_Normalize.normalize
                           [FStarC_TypeChecker_Env.EraseUniverses;
                           FStarC_TypeChecker_Env.Inlining;
                           FStarC_TypeChecker_Env.DontUnfoldAttr
                             [FStarC_Parser_Const.tac_opaque_attr];
                           FStarC_TypeChecker_Env.UnfoldUntil
                             FStarC_Syntax_Syntax.delta_constant] env1.tcenv
                           t1 in
                       let uu___5 =
                         let uu___6 = FStarC_Syntax_Subst.compress res in
                         uu___6.FStarC_Syntax_Syntax.n in
                       (match uu___5 with
                        | FStarC_Syntax_Syntax.Tm_app uu___6 -> true
                        | uu___6 ->
                            ((let uu___8 =
                                let uu___9 =
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term head1 in
                                FStarC_Compiler_Util.format1
                                  "Got a term which might be a non-dependent user-defined data-type %s\n"
                                  uu___9 in
                              FStarC_Errors.log_issue
                                (FStarC_Syntax_Syntax.has_range_syntax ())
                                head1
                                FStarC_Errors_Codes.Warning_NondependentUserDefinedDataType
                                ()
                                (Obj.magic
                                   FStarC_Errors_Msg.is_error_message_string)
                                (Obj.magic uu___8));
                             false))
                     else false)
            | FStarC_Syntax_Syntax.Tm_bvar uu___1 -> true
            | FStarC_Syntax_Syntax.Tm_name uu___1 -> true
            | FStarC_Syntax_Syntax.Tm_uinst (t2, uu___1) ->
                is_valid_application t2
            | uu___1 -> false in
          let uu___ = is_valid_application head in
          if uu___
          then
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStarC_Compiler_List.map
                    (fun uu___4 ->
                       match uu___4 with
                       | (t2, qual) ->
                           let uu___5 = star_type' env1 t2 in (uu___5, qual))
                    args in
                {
                  FStarC_Syntax_Syntax.hd = head;
                  FStarC_Syntax_Syntax.args = uu___3
                } in
              FStarC_Syntax_Syntax.Tm_app uu___2 in
            mk uu___1
          else
            (let uu___2 =
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
               FStarC_Compiler_Util.format1
                 "For now, only [either], [option] and [eq2] are supported in the definition language (got: %s)"
                 uu___3 in
             FStarC_Errors.raise_error0 FStarC_Errors_Codes.Fatal_WrongTerm
               () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic uu___2))
      | FStarC_Syntax_Syntax.Tm_bvar uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_name uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_type uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_fvar uu___ -> t1
      | FStarC_Syntax_Syntax.Tm_abs
          { FStarC_Syntax_Syntax.bs = binders;
            FStarC_Syntax_Syntax.body = repr;
            FStarC_Syntax_Syntax.rc_opt = something;_}
          ->
          let uu___ = FStarC_Syntax_Subst.open_term binders repr in
          (match uu___ with
           | (binders1, repr1) ->
               let env2 =
                 let uu___1 =
                   FStarC_TypeChecker_Env.push_binders env1.tcenv binders1 in
                 {
                   tcenv = uu___1;
                   subst = (env1.subst);
                   tc_const = (env1.tc_const)
                 } in
               let repr2 = star_type' env2 repr1 in
               FStarC_Syntax_Util.abs binders1 repr2 something)
      | FStarC_Syntax_Syntax.Tm_refine
          { FStarC_Syntax_Syntax.b = x; FStarC_Syntax_Syntax.phi = t2;_} when
          false ->
          let x1 = FStarC_Syntax_Syntax.freshen_bv x in
          let sort = star_type' env1 x1.FStarC_Syntax_Syntax.sort in
          let subst = [FStarC_Syntax_Syntax.DB (Prims.int_zero, x1)] in
          let t3 = FStarC_Syntax_Subst.subst subst t2 in
          let t4 = star_type' env1 t3 in
          let subst1 = [FStarC_Syntax_Syntax.NM (x1, Prims.int_zero)] in
          let t5 = FStarC_Syntax_Subst.subst subst1 t4 in
          mk
            (FStarC_Syntax_Syntax.Tm_refine
               {
                 FStarC_Syntax_Syntax.b =
                   {
                     FStarC_Syntax_Syntax.ppname =
                       (x1.FStarC_Syntax_Syntax.ppname);
                     FStarC_Syntax_Syntax.index =
                       (x1.FStarC_Syntax_Syntax.index);
                     FStarC_Syntax_Syntax.sort = sort
                   };
                 FStarC_Syntax_Syntax.phi = t5
               })
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = t2; FStarC_Syntax_Syntax.meta = m;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = star_type' env1 t2 in
              {
                FStarC_Syntax_Syntax.tm2 = uu___2;
                FStarC_Syntax_Syntax.meta = m
              } in
            FStarC_Syntax_Syntax.Tm_meta uu___1 in
          mk uu___
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = e;
            FStarC_Syntax_Syntax.asc =
              (FStar_Pervasives.Inl t2, FStar_Pervasives_Native.None, use_eq);
            FStarC_Syntax_Syntax.eff_opt = something;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = star_type' env1 e in
              let uu___3 =
                let uu___4 =
                  let uu___5 = star_type' env1 t2 in
                  FStar_Pervasives.Inl uu___5 in
                (uu___4, FStar_Pervasives_Native.None, use_eq) in
              {
                FStarC_Syntax_Syntax.tm = uu___2;
                FStarC_Syntax_Syntax.asc = uu___3;
                FStarC_Syntax_Syntax.eff_opt = something
              } in
            FStarC_Syntax_Syntax.Tm_ascribed uu___1 in
          mk uu___
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = e;
            FStarC_Syntax_Syntax.asc =
              (FStar_Pervasives.Inr c, FStar_Pervasives_Native.None, use_eq);
            FStarC_Syntax_Syntax.eff_opt = something;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 = star_type' env1 e in
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    star_type' env1 (FStarC_Syntax_Util.comp_result c) in
                  FStar_Pervasives.Inl uu___5 in
                (uu___4, FStar_Pervasives_Native.None, use_eq) in
              {
                FStarC_Syntax_Syntax.tm = uu___2;
                FStarC_Syntax_Syntax.asc = uu___3;
                FStarC_Syntax_Syntax.eff_opt = something
              } in
            FStarC_Syntax_Syntax.Tm_ascribed uu___1 in
          mk uu___
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = uu___;
            FStarC_Syntax_Syntax.asc =
              (uu___1, FStar_Pervasives_Native.Some uu___2, uu___3);
            FStarC_Syntax_Syntax.eff_opt = uu___4;_}
          ->
          let uu___5 =
            let uu___6 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format1
              "Ascriptions with tactics are outside of the definition language: %s"
              uu___6 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___5)
      | FStarC_Syntax_Syntax.Tm_refine uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "%s is outside of the definition language: %s" uu___2 uu___3 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___1)
      | FStarC_Syntax_Syntax.Tm_uinst uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "%s is outside of the definition language: %s" uu___2 uu___3 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___1)
      | FStarC_Syntax_Syntax.Tm_quoted uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "%s is outside of the definition language: %s" uu___2 uu___3 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___1)
      | FStarC_Syntax_Syntax.Tm_constant uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "%s is outside of the definition language: %s" uu___2 uu___3 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___1)
      | FStarC_Syntax_Syntax.Tm_match uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "%s is outside of the definition language: %s" uu___2 uu___3 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___1)
      | FStarC_Syntax_Syntax.Tm_let uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "%s is outside of the definition language: %s" uu___2 uu___3 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___1)
      | FStarC_Syntax_Syntax.Tm_uvar uu___ ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "%s is outside of the definition language: %s" uu___2 uu___3 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___1)
      | FStarC_Syntax_Syntax.Tm_unknown ->
          let uu___ =
            let uu___1 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___2 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "%s is outside of the definition language: %s" uu___1 uu___2 in
          FStarC_Errors.raise_error0
            FStarC_Errors_Codes.Fatal_TermOutsideOfDefLanguage ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___)
      | FStarC_Syntax_Syntax.Tm_lazy i ->
          let uu___ = FStarC_Syntax_Util.unfold_lazy i in
          star_type' env1 uu___
      | FStarC_Syntax_Syntax.Tm_delayed uu___ -> failwith "impossible"
let (is_monadic :
  FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> failwith "un-annotated lambda?!"
    | FStar_Pervasives_Native.Some rc ->
        FStarC_Compiler_Util.for_some
          (fun uu___1 ->
             match uu___1 with
             | FStarC_Syntax_Syntax.CPS -> true
             | uu___2 -> false) rc.FStarC_Syntax_Syntax.residual_flags
let rec (is_C : FStarC_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStarC_Syntax_Subst.compress t in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = head; FStarC_Syntax_Syntax.args = args;_}
        when FStarC_Syntax_Util.is_tuple_constructor head ->
        let r =
          let uu___1 =
            let uu___2 = FStarC_Compiler_List.hd args in
            FStar_Pervasives_Native.fst uu___2 in
          is_C uu___1 in
        if r
        then
          ((let uu___2 =
              let uu___3 =
                FStarC_Compiler_List.for_all
                  (fun uu___4 -> match uu___4 with | (h, uu___5) -> is_C h)
                  args in
              Prims.op_Negation uu___3 in
            if uu___2
            then
              let uu___3 =
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                FStarC_Compiler_Util.format1 "Not a C-type (A * C): %s"
                  uu___4 in
              FStarC_Errors.raise_error
                (FStarC_Syntax_Syntax.has_range_syntax ()) t
                FStarC_Errors_Codes.Error_UnexpectedDM4FType ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___3)
            else ());
           true)
        else
          ((let uu___3 =
              let uu___4 =
                FStarC_Compiler_List.for_all
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
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                FStarC_Compiler_Util.format1 "Not a C-type (C * A): %s"
                  uu___5 in
              FStarC_Errors.raise_error
                (FStarC_Syntax_Syntax.has_range_syntax ()) t
                FStarC_Errors_Codes.Error_UnexpectedDM4FType ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___4)
            else ());
           false)
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = binders;
          FStarC_Syntax_Syntax.comp = comp;_}
        ->
        let uu___1 = nm_of_comp comp in
        (match uu___1 with
         | M t1 ->
             ((let uu___3 = is_C t1 in
               if uu___3
               then
                 let uu___4 =
                   let uu___5 =
                     FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                       t1 in
                   FStarC_Compiler_Util.format1 "Not a C-type (C -> C): %s"
                     uu___5 in
                 FStarC_Errors.raise_error
                   (FStarC_Syntax_Syntax.has_range_syntax ()) t1
                   FStarC_Errors_Codes.Error_UnexpectedDM4FType ()
                   (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                   (Obj.magic uu___4)
               else ());
              true)
         | N t1 -> is_C t1)
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t1;
          FStarC_Syntax_Syntax.meta = uu___1;_}
        -> is_C t1
    | FStarC_Syntax_Syntax.Tm_uinst (t1, uu___1) -> is_C t1
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t1; FStarC_Syntax_Syntax.asc = uu___1;
          FStarC_Syntax_Syntax.eff_opt = uu___2;_}
        -> is_C t1
    | uu___1 -> false
let (mk_return :
  env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  =
  fun env1 ->
    fun t ->
      fun e ->
        let mk x = FStarC_Syntax_Syntax.mk x e.FStarC_Syntax_Syntax.pos in
        let p_type = mk_star_to_type mk env1 t in
        let p =
          FStarC_Syntax_Syntax.gen_bv "p'" FStar_Pervasives_Native.None
            p_type in
        let body =
          let uu___ =
            let uu___1 =
              let uu___2 = FStarC_Syntax_Syntax.bv_to_name p in
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Syntax.as_aqual_implicit false in
                  (e, uu___5) in
                [uu___4] in
              {
                FStarC_Syntax_Syntax.hd = uu___2;
                FStarC_Syntax_Syntax.args = uu___3
              } in
            FStarC_Syntax_Syntax.Tm_app uu___1 in
          mk uu___ in
        let uu___ = let uu___1 = FStarC_Syntax_Syntax.mk_binder p in [uu___1] in
        FStarC_Syntax_Util.abs uu___ body
          (FStar_Pervasives_Native.Some
             (FStarC_Syntax_Util.residual_tot FStarC_Syntax_Util.ktype0))
let (is_unknown : FStarC_Syntax_Syntax.term' -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_unknown -> true
    | uu___1 -> false
let rec (check :
  env ->
    FStarC_Syntax_Syntax.term ->
      nm -> (nm * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      fun context_nm ->
        let return_if uu___ =
          match uu___ with
          | (rec_nm, s_e, u_e) ->
              let check1 t1 t2 =
                let uu___1 =
                  (Prims.op_Negation (is_unknown t2.FStarC_Syntax_Syntax.n))
                    &&
                    (let uu___2 =
                       let uu___3 =
                         FStarC_TypeChecker_Rel.teq env1.tcenv t1 t2 in
                       FStarC_TypeChecker_Env.is_trivial uu___3 in
                     Prims.op_Negation uu___2) in
                if uu___1
                then
                  let uu___2 =
                    let uu___3 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term e in
                    let uu___4 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term t1 in
                    let uu___5 =
                      FStarC_Class_Show.show
                        FStarC_Syntax_Print.showable_term t2 in
                    FStarC_Compiler_Util.format3
                      "[check]: the expression [%s] has type [%s] but should have type [%s]"
                      uu___3 uu___4 uu___5 in
                  FStarC_Errors.raise_error0
                    FStarC_Errors_Codes.Fatal_TypeMismatch ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                    (Obj.magic uu___2)
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
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term e in
                     let uu___3 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term t1 in
                     let uu___4 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term t2 in
                     FStarC_Compiler_Util.format3
                       "[check %s]: got an effectful computation [%s] in lieu of a pure computation [%s]"
                       uu___2 uu___3 uu___4 in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Fatal_EffectfulAndPureComputationMismatch
                     () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___1)) in
        let ensure_m env2 e2 =
          let strip_m uu___ =
            match uu___ with
            | (M t, s_e, u_e) -> (t, s_e, u_e)
            | uu___1 -> failwith "impossible" in
          match context_nm with
          | N t ->
              let uu___ =
                let uu___1 =
                  FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
                Prims.strcat
                  "let-bound monadic body has a non-monadic continuation or a branch of a match is monadic and the others aren't : "
                  uu___1 in
              FStarC_Errors.raise_error
                (FStarC_Syntax_Syntax.has_range_syntax ()) e2
                FStarC_Errors_Codes.Fatal_LetBoundMonadicMismatch ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                (Obj.magic uu___)
          | M uu___ ->
              let uu___1 = check env2 e2 context_nm in strip_m uu___1 in
        let uu___ =
          let uu___1 = FStarC_Syntax_Subst.compress e in
          uu___1.FStarC_Syntax_Syntax.n in
        match uu___ with
        | FStarC_Syntax_Syntax.Tm_bvar uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStarC_Syntax_Syntax.Tm_name uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStarC_Syntax_Syntax.Tm_fvar uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStarC_Syntax_Syntax.Tm_abs uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStarC_Syntax_Syntax.Tm_constant uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStarC_Syntax_Syntax.Tm_quoted uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStarC_Syntax_Syntax.Tm_app uu___1 ->
            let uu___2 = infer env1 e in return_if uu___2
        | FStarC_Syntax_Syntax.Tm_lazy i ->
            let uu___1 = FStarC_Syntax_Util.unfold_lazy i in
            check env1 uu___1 context_nm
        | FStarC_Syntax_Syntax.Tm_let
            { FStarC_Syntax_Syntax.lbs = (false, binding::[]);
              FStarC_Syntax_Syntax.body1 = e2;_}
            ->
            mk_let env1 binding e2
              (fun env2 -> fun e21 -> check env2 e21 context_nm) ensure_m
        | FStarC_Syntax_Syntax.Tm_match
            { FStarC_Syntax_Syntax.scrutinee = e0;
              FStarC_Syntax_Syntax.ret_opt = uu___1;
              FStarC_Syntax_Syntax.brs = branches;
              FStarC_Syntax_Syntax.rc_opt1 = uu___2;_}
            ->
            mk_match env1 e0 branches
              (fun env2 -> fun body -> check env2 body context_nm)
        | FStarC_Syntax_Syntax.Tm_meta
            { FStarC_Syntax_Syntax.tm2 = e1;
              FStarC_Syntax_Syntax.meta = uu___1;_}
            -> check env1 e1 context_nm
        | FStarC_Syntax_Syntax.Tm_uinst (e1, uu___1) ->
            check env1 e1 context_nm
        | FStarC_Syntax_Syntax.Tm_ascribed
            { FStarC_Syntax_Syntax.tm = e1;
              FStarC_Syntax_Syntax.asc = uu___1;
              FStarC_Syntax_Syntax.eff_opt = uu___2;_}
            -> check env1 e1 context_nm
        | FStarC_Syntax_Syntax.Tm_let uu___1 ->
            let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
              FStarC_Compiler_Util.format1 "[check]: Tm_let %s" uu___3 in
            failwith uu___2
        | FStarC_Syntax_Syntax.Tm_type uu___1 ->
            failwith "impossible (DM stratification)"
        | FStarC_Syntax_Syntax.Tm_arrow uu___1 ->
            failwith "impossible (DM stratification)"
        | FStarC_Syntax_Syntax.Tm_refine uu___1 ->
            let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
              FStarC_Compiler_Util.format1 "[check]: Tm_refine %s" uu___3 in
            failwith uu___2
        | FStarC_Syntax_Syntax.Tm_uvar uu___1 ->
            let uu___2 =
              let uu___3 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
              FStarC_Compiler_Util.format1 "[check]: Tm_uvar %s" uu___3 in
            failwith uu___2
        | FStarC_Syntax_Syntax.Tm_delayed uu___1 ->
            failwith "impossible (compressed)"
        | FStarC_Syntax_Syntax.Tm_unknown ->
            let uu___1 =
              let uu___2 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
              FStarC_Compiler_Util.format1 "[check]: Tm_unknown %s" uu___2 in
            failwith uu___1
and (infer :
  env ->
    FStarC_Syntax_Syntax.term ->
      (nm * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mk x = FStarC_Syntax_Syntax.mk x e.FStarC_Syntax_Syntax.pos in
      let normalize =
        FStarC_TypeChecker_Normalize.normalize
          [FStarC_TypeChecker_Env.Beta;
          FStarC_TypeChecker_Env.Eager_unfolding;
          FStarC_TypeChecker_Env.DontUnfoldAttr
            [FStarC_Parser_Const.tac_opaque_attr];
          FStarC_TypeChecker_Env.UnfoldUntil
            FStarC_Syntax_Syntax.delta_constant;
          FStarC_TypeChecker_Env.EraseUniverses] env1.tcenv in
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress e in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_bvar bv ->
          failwith "I failed to open a binder... boo"
      | FStarC_Syntax_Syntax.Tm_name bv ->
          ((N (bv.FStarC_Syntax_Syntax.sort)), e, e)
      | FStarC_Syntax_Syntax.Tm_lazy i ->
          let uu___1 = FStarC_Syntax_Util.unfold_lazy i in infer env1 uu___1
      | FStarC_Syntax_Syntax.Tm_abs
          { FStarC_Syntax_Syntax.bs = binders;
            FStarC_Syntax_Syntax.body = body;
            FStarC_Syntax_Syntax.rc_opt = rc_opt;_}
          ->
          let subst_rc_opt subst rc_opt1 =
            match rc_opt1 with
            | FStar_Pervasives_Native.Some
                { FStarC_Syntax_Syntax.residual_effect = uu___1;
                  FStarC_Syntax_Syntax.residual_typ =
                    FStar_Pervasives_Native.None;
                  FStarC_Syntax_Syntax.residual_flags = uu___2;_}
                -> rc_opt1
            | FStar_Pervasives_Native.None -> rc_opt1
            | FStar_Pervasives_Native.Some rc ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        FStarC_Compiler_Util.must
                          rc.FStarC_Syntax_Syntax.residual_typ in
                      FStarC_Syntax_Subst.subst subst uu___4 in
                    FStar_Pervasives_Native.Some uu___3 in
                  {
                    FStarC_Syntax_Syntax.residual_effect =
                      (rc.FStarC_Syntax_Syntax.residual_effect);
                    FStarC_Syntax_Syntax.residual_typ = uu___2;
                    FStarC_Syntax_Syntax.residual_flags =
                      (rc.FStarC_Syntax_Syntax.residual_flags)
                  } in
                FStar_Pervasives_Native.Some uu___1 in
          let binders1 = FStarC_Syntax_Subst.open_binders binders in
          let subst = FStarC_Syntax_Subst.opening_of_binders binders1 in
          let body1 = FStarC_Syntax_Subst.subst subst body in
          let rc_opt1 = subst_rc_opt subst rc_opt in
          let env2 =
            let uu___1 =
              FStarC_TypeChecker_Env.push_binders env1.tcenv binders1 in
            {
              tcenv = uu___1;
              subst = (env1.subst);
              tc_const = (env1.tc_const)
            } in
          let s_binders =
            FStarC_Compiler_List.map
              (fun b ->
                 let sort =
                   star_type' env2
                     (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                 {
                   FStarC_Syntax_Syntax.binder_bv =
                     (let uu___1 = b.FStarC_Syntax_Syntax.binder_bv in
                      {
                        FStarC_Syntax_Syntax.ppname =
                          (uu___1.FStarC_Syntax_Syntax.ppname);
                        FStarC_Syntax_Syntax.index =
                          (uu___1.FStarC_Syntax_Syntax.index);
                        FStarC_Syntax_Syntax.sort = sort
                      });
                   FStarC_Syntax_Syntax.binder_qual =
                     (b.FStarC_Syntax_Syntax.binder_qual);
                   FStarC_Syntax_Syntax.binder_positivity =
                     (b.FStarC_Syntax_Syntax.binder_positivity);
                   FStarC_Syntax_Syntax.binder_attrs =
                     (b.FStarC_Syntax_Syntax.binder_attrs)
                 }) binders1 in
          let uu___1 =
            FStarC_Compiler_List.fold_left
              (fun uu___2 ->
                 fun uu___3 ->
                   match (uu___2, uu___3) with
                   | ((env3, acc),
                      { FStarC_Syntax_Syntax.binder_bv = bv;
                        FStarC_Syntax_Syntax.binder_qual = uu___4;
                        FStarC_Syntax_Syntax.binder_positivity = uu___5;
                        FStarC_Syntax_Syntax.binder_attrs = uu___6;_})
                       ->
                       let c = bv.FStarC_Syntax_Syntax.sort in
                       let uu___7 = is_C c in
                       if uu___7
                       then
                         let xw =
                           let uu___8 =
                             let uu___9 =
                               FStarC_Ident.string_of_id
                                 bv.FStarC_Syntax_Syntax.ppname in
                             Prims.strcat uu___9 "__w" in
                           let uu___9 = star_type' env3 c in
                           FStarC_Syntax_Syntax.gen_bv uu___8
                             FStar_Pervasives_Native.None uu___9 in
                         let x =
                           let uu___8 =
                             let uu___9 = FStarC_Syntax_Syntax.bv_to_name xw in
                             trans_F_ env3 c uu___9 in
                           {
                             FStarC_Syntax_Syntax.ppname =
                               (bv.FStarC_Syntax_Syntax.ppname);
                             FStarC_Syntax_Syntax.index =
                               (bv.FStarC_Syntax_Syntax.index);
                             FStarC_Syntax_Syntax.sort = uu___8
                           } in
                         let env4 =
                           let uu___8 =
                             let uu___9 =
                               let uu___10 =
                                 let uu___11 =
                                   FStarC_Syntax_Syntax.bv_to_name xw in
                                 (bv, uu___11) in
                               FStarC_Syntax_Syntax.NT uu___10 in
                             uu___9 :: (env3.subst) in
                           {
                             tcenv = (env3.tcenv);
                             subst = uu___8;
                             tc_const = (env3.tc_const)
                           } in
                         let uu___8 =
                           let uu___9 = FStarC_Syntax_Syntax.mk_binder x in
                           let uu___10 =
                             let uu___11 = FStarC_Syntax_Syntax.mk_binder xw in
                             uu___11 :: acc in
                           uu___9 :: uu___10 in
                         (env4, uu___8)
                       else
                         (let x =
                            let uu___9 =
                              star_type' env3 bv.FStarC_Syntax_Syntax.sort in
                            {
                              FStarC_Syntax_Syntax.ppname =
                                (bv.FStarC_Syntax_Syntax.ppname);
                              FStarC_Syntax_Syntax.index =
                                (bv.FStarC_Syntax_Syntax.index);
                              FStarC_Syntax_Syntax.sort = uu___9
                            } in
                          let uu___9 =
                            let uu___10 = FStarC_Syntax_Syntax.mk_binder x in
                            uu___10 :: acc in
                          (env3, uu___9))) (env2, []) binders1 in
          (match uu___1 with
           | (env3, u_binders) ->
               let u_binders1 = FStarC_Compiler_List.rev u_binders in
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
                    let t = FStarC_Syntax_Util.arrow binders1 comp in
                    let s_rc_opt =
                      match rc_opt1 with
                      | FStar_Pervasives_Native.None ->
                          FStar_Pervasives_Native.None
                      | FStar_Pervasives_Native.Some rc ->
                          (match rc.FStarC_Syntax_Syntax.residual_typ with
                           | FStar_Pervasives_Native.None ->
                               let rc1 =
                                 let uu___3 =
                                   FStarC_Compiler_Util.for_some
                                     (fun uu___4 ->
                                        match uu___4 with
                                        | FStarC_Syntax_Syntax.CPS -> true
                                        | uu___5 -> false)
                                     rc.FStarC_Syntax_Syntax.residual_flags in
                                 if uu___3
                                 then
                                   let uu___4 =
                                     FStarC_Compiler_List.filter
                                       (fun uu___5 ->
                                          match uu___5 with
                                          | FStarC_Syntax_Syntax.CPS -> false
                                          | uu___6 -> true)
                                       rc.FStarC_Syntax_Syntax.residual_flags in
                                   FStarC_Syntax_Util.mk_residual_comp
                                     FStarC_Parser_Const.effect_Tot_lid
                                     FStar_Pervasives_Native.None uu___4
                                 else rc in
                               FStar_Pervasives_Native.Some rc1
                           | FStar_Pervasives_Native.Some rt ->
                               let rt1 =
                                 let uu___3 = get_env env3 in
                                 FStarC_TypeChecker_Normalize.normalize
                                   [FStarC_TypeChecker_Env.Beta;
                                   FStarC_TypeChecker_Env.Eager_unfolding;
                                   FStarC_TypeChecker_Env.DontUnfoldAttr
                                     [FStarC_Parser_Const.tac_opaque_attr];
                                   FStarC_TypeChecker_Env.UnfoldUntil
                                     FStarC_Syntax_Syntax.delta_constant;
                                   FStarC_TypeChecker_Env.EraseUniverses]
                                   uu___3 rt in
                               let uu___3 =
                                 FStarC_Compiler_Util.for_some
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | FStarC_Syntax_Syntax.CPS -> true
                                      | uu___5 -> false)
                                   rc.FStarC_Syntax_Syntax.residual_flags in
                               if uu___3
                               then
                                 let flags =
                                   FStarC_Compiler_List.filter
                                     (fun uu___4 ->
                                        match uu___4 with
                                        | FStarC_Syntax_Syntax.CPS -> false
                                        | uu___5 -> true)
                                     rc.FStarC_Syntax_Syntax.residual_flags in
                                 let uu___4 =
                                   let uu___5 =
                                     let uu___6 = double_star rt1 in
                                     FStar_Pervasives_Native.Some uu___6 in
                                   FStarC_Syntax_Util.mk_residual_comp
                                     FStarC_Parser_Const.effect_Tot_lid
                                     uu___5 flags in
                                 FStar_Pervasives_Native.Some uu___4
                               else
                                 (let uu___5 =
                                    let uu___6 =
                                      let uu___7 = star_type' env3 rt1 in
                                      FStar_Pervasives_Native.Some uu___7 in
                                    {
                                      FStarC_Syntax_Syntax.residual_effect =
                                        (rc.FStarC_Syntax_Syntax.residual_effect);
                                      FStarC_Syntax_Syntax.residual_typ =
                                        uu___6;
                                      FStarC_Syntax_Syntax.residual_flags =
                                        (rc.FStarC_Syntax_Syntax.residual_flags)
                                    } in
                                  FStar_Pervasives_Native.Some uu___5)) in
                    let uu___3 =
                      let comp1 =
                        let uu___4 = is_monadic rc_opt1 in
                        let uu___5 =
                          FStarC_Syntax_Subst.subst env3.subst s_body in
                        trans_G env3 (FStarC_Syntax_Util.comp_result comp)
                          uu___4 uu___5 in
                      let uu___4 =
                        FStarC_Syntax_Util.ascribe u_body
                          ((FStar_Pervasives.Inr comp1),
                            FStar_Pervasives_Native.None, false) in
                      let uu___5 =
                        let uu___6 =
                          FStarC_Syntax_Util.residual_comp_of_comp comp1 in
                        FStar_Pervasives_Native.Some uu___6 in
                      (uu___4, uu___5) in
                    (match uu___3 with
                     | (u_body1, u_rc_opt) ->
                         let s_body1 =
                           FStarC_Syntax_Subst.close s_binders s_body in
                         let s_binders1 =
                           FStarC_Syntax_Subst.close_binders s_binders in
                         let s_term =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   FStarC_Syntax_Subst.closing_of_binders
                                     s_binders1 in
                                 subst_rc_opt uu___7 s_rc_opt in
                               {
                                 FStarC_Syntax_Syntax.bs = s_binders1;
                                 FStarC_Syntax_Syntax.body = s_body1;
                                 FStarC_Syntax_Syntax.rc_opt = uu___6
                               } in
                             FStarC_Syntax_Syntax.Tm_abs uu___5 in
                           mk uu___4 in
                         let u_body2 =
                           FStarC_Syntax_Subst.close u_binders1 u_body1 in
                         let u_binders2 =
                           FStarC_Syntax_Subst.close_binders u_binders1 in
                         let u_term =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   FStarC_Syntax_Subst.closing_of_binders
                                     u_binders2 in
                                 subst_rc_opt uu___7 u_rc_opt in
                               {
                                 FStarC_Syntax_Syntax.bs = u_binders2;
                                 FStarC_Syntax_Syntax.body = u_body2;
                                 FStarC_Syntax_Syntax.rc_opt = uu___6
                               } in
                             FStarC_Syntax_Syntax.Tm_abs uu___5 in
                           mk uu___4 in
                         ((N t), s_term, u_term))))
      | FStarC_Syntax_Syntax.Tm_fvar
          {
            FStarC_Syntax_Syntax.fv_name =
              { FStarC_Syntax_Syntax.v = lid;
                FStarC_Syntax_Syntax.p = uu___1;_};
            FStarC_Syntax_Syntax.fv_qual = uu___2;_}
          ->
          let uu___3 =
            let uu___4 = FStarC_TypeChecker_Env.lookup_lid env1.tcenv lid in
            FStar_Pervasives_Native.fst uu___4 in
          (match uu___3 with
           | (uu___4, t) ->
               let uu___5 = let uu___6 = normalize t in N uu___6 in
               (uu___5, e, e))
      | FStarC_Syntax_Syntax.Tm_app
          {
            FStarC_Syntax_Syntax.hd =
              {
                FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                  (FStarC_Const.Const_range_of);
                FStarC_Syntax_Syntax.pos = uu___1;
                FStarC_Syntax_Syntax.vars = uu___2;
                FStarC_Syntax_Syntax.hash_code = uu___3;_};
            FStarC_Syntax_Syntax.args = a::hd::rest;_}
          ->
          let rest1 = hd :: rest in
          let uu___4 = FStarC_Syntax_Util.head_and_args e in
          (match uu___4 with
           | (unary_op, uu___5) ->
               let head =
                 mk
                   (FStarC_Syntax_Syntax.Tm_app
                      {
                        FStarC_Syntax_Syntax.hd = unary_op;
                        FStarC_Syntax_Syntax.args = [a]
                      }) in
               let t =
                 mk
                   (FStarC_Syntax_Syntax.Tm_app
                      {
                        FStarC_Syntax_Syntax.hd = head;
                        FStarC_Syntax_Syntax.args = rest1
                      }) in
               infer env1 t)
      | FStarC_Syntax_Syntax.Tm_app
          {
            FStarC_Syntax_Syntax.hd =
              {
                FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                  (FStarC_Const.Const_set_range_of);
                FStarC_Syntax_Syntax.pos = uu___1;
                FStarC_Syntax_Syntax.vars = uu___2;
                FStarC_Syntax_Syntax.hash_code = uu___3;_};
            FStarC_Syntax_Syntax.args = a1::a2::hd::rest;_}
          ->
          let rest1 = hd :: rest in
          let uu___4 = FStarC_Syntax_Util.head_and_args e in
          (match uu___4 with
           | (unary_op, uu___5) ->
               let head =
                 mk
                   (FStarC_Syntax_Syntax.Tm_app
                      {
                        FStarC_Syntax_Syntax.hd = unary_op;
                        FStarC_Syntax_Syntax.args = [a1; a2]
                      }) in
               let t =
                 mk
                   (FStarC_Syntax_Syntax.Tm_app
                      {
                        FStarC_Syntax_Syntax.hd = head;
                        FStarC_Syntax_Syntax.args = rest1
                      }) in
               infer env1 t)
      | FStarC_Syntax_Syntax.Tm_app
          {
            FStarC_Syntax_Syntax.hd =
              {
                FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                  (FStarC_Const.Const_range_of);
                FStarC_Syntax_Syntax.pos = uu___1;
                FStarC_Syntax_Syntax.vars = uu___2;
                FStarC_Syntax_Syntax.hash_code = uu___3;_};
            FStarC_Syntax_Syntax.args = (a, FStar_Pervasives_Native.None)::[];_}
          ->
          let uu___4 = infer env1 a in
          (match uu___4 with
           | (t, s, u) ->
               let uu___5 = FStarC_Syntax_Util.head_and_args e in
               (match uu___5 with
                | (head, uu___6) ->
                    let uu___7 =
                      let uu___8 =
                        FStarC_Syntax_Syntax.tabbrev
                          FStarC_Parser_Const.range_lid in
                      N uu___8 in
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            let uu___12 = FStarC_Syntax_Syntax.as_arg s in
                            [uu___12] in
                          {
                            FStarC_Syntax_Syntax.hd = head;
                            FStarC_Syntax_Syntax.args = uu___11
                          } in
                        FStarC_Syntax_Syntax.Tm_app uu___10 in
                      mk uu___9 in
                    let uu___9 =
                      let uu___10 =
                        let uu___11 =
                          let uu___12 =
                            let uu___13 = FStarC_Syntax_Syntax.as_arg u in
                            [uu___13] in
                          {
                            FStarC_Syntax_Syntax.hd = head;
                            FStarC_Syntax_Syntax.args = uu___12
                          } in
                        FStarC_Syntax_Syntax.Tm_app uu___11 in
                      mk uu___10 in
                    (uu___7, uu___8, uu___9)))
      | FStarC_Syntax_Syntax.Tm_app
          {
            FStarC_Syntax_Syntax.hd =
              {
                FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                  (FStarC_Const.Const_set_range_of);
                FStarC_Syntax_Syntax.pos = uu___1;
                FStarC_Syntax_Syntax.vars = uu___2;
                FStarC_Syntax_Syntax.hash_code = uu___3;_};
            FStarC_Syntax_Syntax.args = (a1, uu___4)::a2::[];_}
          ->
          let uu___5 = infer env1 a1 in
          (match uu___5 with
           | (t, s, u) ->
               let uu___6 = FStarC_Syntax_Util.head_and_args e in
               (match uu___6 with
                | (head, uu___7) ->
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            let uu___12 = FStarC_Syntax_Syntax.as_arg s in
                            [uu___12; a2] in
                          {
                            FStarC_Syntax_Syntax.hd = head;
                            FStarC_Syntax_Syntax.args = uu___11
                          } in
                        FStarC_Syntax_Syntax.Tm_app uu___10 in
                      mk uu___9 in
                    let uu___9 =
                      let uu___10 =
                        let uu___11 =
                          let uu___12 =
                            let uu___13 = FStarC_Syntax_Syntax.as_arg u in
                            [uu___13; a2] in
                          {
                            FStarC_Syntax_Syntax.hd = head;
                            FStarC_Syntax_Syntax.args = uu___12
                          } in
                        FStarC_Syntax_Syntax.Tm_app uu___11 in
                      mk uu___10 in
                    (t, uu___8, uu___9)))
      | FStarC_Syntax_Syntax.Tm_app
          {
            FStarC_Syntax_Syntax.hd =
              {
                FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                  (FStarC_Const.Const_range_of);
                FStarC_Syntax_Syntax.pos = uu___1;
                FStarC_Syntax_Syntax.vars = uu___2;
                FStarC_Syntax_Syntax.hash_code = uu___3;_};
            FStarC_Syntax_Syntax.args = uu___4;_}
          ->
          let uu___5 =
            let uu___6 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
            FStarC_Compiler_Util.format1 "DMFF: Ill-applied constant %s"
              uu___6 in
          FStarC_Errors.raise_error
            (FStarC_Syntax_Syntax.has_range_syntax ()) e
            FStarC_Errors_Codes.Fatal_IllAppliedConstant ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___5)
      | FStarC_Syntax_Syntax.Tm_app
          {
            FStarC_Syntax_Syntax.hd =
              {
                FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_constant
                  (FStarC_Const.Const_set_range_of);
                FStarC_Syntax_Syntax.pos = uu___1;
                FStarC_Syntax_Syntax.vars = uu___2;
                FStarC_Syntax_Syntax.hash_code = uu___3;_};
            FStarC_Syntax_Syntax.args = uu___4;_}
          ->
          let uu___5 =
            let uu___6 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
            FStarC_Compiler_Util.format1 "DMFF: Ill-applied constant %s"
              uu___6 in
          FStarC_Errors.raise_error
            (FStarC_Syntax_Syntax.has_range_syntax ()) e
            FStarC_Errors_Codes.Fatal_IllAppliedConstant ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___5)
      | FStarC_Syntax_Syntax.Tm_app
          { FStarC_Syntax_Syntax.hd = head;
            FStarC_Syntax_Syntax.args = args;_}
          ->
          let uu___1 = check_n env1 head in
          (match uu___1 with
           | (t_head, s_head, u_head) ->
               let is_arrow t =
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Subst.compress t in
                   uu___3.FStarC_Syntax_Syntax.n in
                 match uu___2 with
                 | FStarC_Syntax_Syntax.Tm_arrow uu___3 -> true
                 | uu___3 -> false in
               let rec flatten t =
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Subst.compress t in
                   uu___3.FStarC_Syntax_Syntax.n in
                 match uu___2 with
                 | FStarC_Syntax_Syntax.Tm_arrow
                     { FStarC_Syntax_Syntax.bs1 = binders;
                       FStarC_Syntax_Syntax.comp =
                         {
                           FStarC_Syntax_Syntax.n =
                             FStarC_Syntax_Syntax.Total t1;
                           FStarC_Syntax_Syntax.pos = uu___3;
                           FStarC_Syntax_Syntax.vars = uu___4;
                           FStarC_Syntax_Syntax.hash_code = uu___5;_};_}
                     when is_arrow t1 ->
                     let uu___6 = flatten t1 in
                     (match uu___6 with
                      | (binders', comp) ->
                          ((FStarC_Compiler_List.op_At binders binders'),
                            comp))
                 | FStarC_Syntax_Syntax.Tm_arrow
                     { FStarC_Syntax_Syntax.bs1 = binders;
                       FStarC_Syntax_Syntax.comp = comp;_}
                     -> (binders, comp)
                 | FStarC_Syntax_Syntax.Tm_ascribed
                     { FStarC_Syntax_Syntax.tm = e1;
                       FStarC_Syntax_Syntax.asc = uu___3;
                       FStarC_Syntax_Syntax.eff_opt = uu___4;_}
                     -> flatten e1
                 | uu___3 ->
                     let uu___4 =
                       let uu___5 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_term t_head in
                       FStarC_Compiler_Util.format1 "%s: not a function type"
                         uu___5 in
                     FStarC_Errors.raise_error0
                       FStarC_Errors_Codes.Fatal_NotFunctionType ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                       (Obj.magic uu___4) in
               let uu___2 = flatten t_head in
               (match uu___2 with
                | (binders, comp) ->
                    let n = FStarC_Compiler_List.length binders in
                    let n' = FStarC_Compiler_List.length args in
                    (if
                       (FStarC_Compiler_List.length binders) <
                         (FStarC_Compiler_List.length args)
                     then
                       (let uu___4 =
                          let uu___5 = FStarC_Compiler_Util.string_of_int n in
                          let uu___6 =
                            FStarC_Compiler_Util.string_of_int (n' - n) in
                          let uu___7 =
                            FStarC_Class_Show.show
                              FStarC_Class_Show.showable_nat n in
                          FStarC_Compiler_Util.format3
                            "The head of this application, after being applied to %s arguments, is an effectful computation (leaving %s arguments to be applied). Please let-bind the head applied to the %s first arguments."
                            uu___5 uu___6 uu___7 in
                        FStarC_Errors.raise_error0
                          FStarC_Errors_Codes.Fatal_BinderAndArgsLengthMismatch
                          ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_string)
                          (Obj.magic uu___4))
                     else ();
                     (let uu___4 = FStarC_Syntax_Subst.open_comp binders comp in
                      match uu___4 with
                      | (binders1, comp1) ->
                          let rec final_type subst uu___5 args1 =
                            match uu___5 with
                            | (binders2, comp2) ->
                                (match (binders2, args1) with
                                 | ([], []) ->
                                     let uu___6 =
                                       FStarC_Syntax_Subst.subst_comp subst
                                         comp2 in
                                     nm_of_comp uu___6
                                 | (binders3, []) ->
                                     let uu___6 =
                                       let uu___7 =
                                         let uu___8 =
                                           let uu___9 =
                                             mk
                                               (FStarC_Syntax_Syntax.Tm_arrow
                                                  {
                                                    FStarC_Syntax_Syntax.bs1
                                                      = binders3;
                                                    FStarC_Syntax_Syntax.comp
                                                      = comp2
                                                  }) in
                                           FStarC_Syntax_Subst.subst subst
                                             uu___9 in
                                         FStarC_Syntax_Subst.compress uu___8 in
                                       uu___7.FStarC_Syntax_Syntax.n in
                                     (match uu___6 with
                                      | FStarC_Syntax_Syntax.Tm_arrow
                                          {
                                            FStarC_Syntax_Syntax.bs1 =
                                              binders4;
                                            FStarC_Syntax_Syntax.comp = comp3;_}
                                          ->
                                          let uu___7 =
                                            let uu___8 =
                                              let uu___9 =
                                                let uu___10 =
                                                  FStarC_Syntax_Subst.close_comp
                                                    binders4 comp3 in
                                                {
                                                  FStarC_Syntax_Syntax.bs1 =
                                                    binders4;
                                                  FStarC_Syntax_Syntax.comp =
                                                    uu___10
                                                } in
                                              FStarC_Syntax_Syntax.Tm_arrow
                                                uu___9 in
                                            mk uu___8 in
                                          N uu___7
                                      | uu___7 -> failwith "wat?")
                                 | ([], uu___6::uu___7) ->
                                     failwith "just checked that?!"
                                 | ({ FStarC_Syntax_Syntax.binder_bv = bv;
                                      FStarC_Syntax_Syntax.binder_qual =
                                        uu___6;
                                      FStarC_Syntax_Syntax.binder_positivity
                                        = uu___7;
                                      FStarC_Syntax_Syntax.binder_attrs =
                                        uu___8;_}::binders3,
                                    (arg, uu___9)::args2) ->
                                     final_type
                                       ((FStarC_Syntax_Syntax.NT (bv, arg))
                                       :: subst) (binders3, comp2) args2) in
                          let final_type1 =
                            final_type [] (binders1, comp1) args in
                          let uu___5 =
                            FStarC_Compiler_List.splitAt n' binders1 in
                          (match uu___5 with
                           | (binders2, uu___6) ->
                               let uu___7 =
                                 let uu___8 =
                                   FStarC_Compiler_List.map2
                                     (fun uu___9 ->
                                        fun uu___10 ->
                                          match (uu___9, uu___10) with
                                          | ({
                                               FStarC_Syntax_Syntax.binder_bv
                                                 = bv;
                                               FStarC_Syntax_Syntax.binder_qual
                                                 = uu___11;
                                               FStarC_Syntax_Syntax.binder_positivity
                                                 = uu___12;
                                               FStarC_Syntax_Syntax.binder_attrs
                                                 = uu___13;_},
                                             (arg, q)) ->
                                              let uu___14 =
                                                let uu___15 =
                                                  FStarC_Syntax_Subst.compress
                                                    bv.FStarC_Syntax_Syntax.sort in
                                                uu___15.FStarC_Syntax_Syntax.n in
                                              (match uu___14 with
                                               | FStarC_Syntax_Syntax.Tm_type
                                                   uu___15 ->
                                                   let uu___16 =
                                                     let uu___17 =
                                                       star_type' env1 arg in
                                                     (uu___17, q) in
                                                   (uu___16, [(arg, q)])
                                               | uu___15 ->
                                                   let uu___16 =
                                                     check_n env1 arg in
                                                   (match uu___16 with
                                                    | (uu___17, s_arg, u_arg)
                                                        ->
                                                        let uu___18 =
                                                          let uu___19 =
                                                            is_C
                                                              bv.FStarC_Syntax_Syntax.sort in
                                                          if uu___19
                                                          then
                                                            let uu___20 =
                                                              let uu___21 =
                                                                FStarC_Syntax_Subst.subst
                                                                  env1.subst
                                                                  s_arg in
                                                              (uu___21, q) in
                                                            [uu___20;
                                                            (u_arg, q)]
                                                          else [(u_arg, q)] in
                                                        ((s_arg, q), uu___18))))
                                     binders2 args in
                                 FStarC_Compiler_List.split uu___8 in
                               (match uu___7 with
                                | (s_args, u_args) ->
                                    let u_args1 =
                                      FStarC_Compiler_List.flatten u_args in
                                    let uu___8 =
                                      mk
                                        (FStarC_Syntax_Syntax.Tm_app
                                           {
                                             FStarC_Syntax_Syntax.hd = s_head;
                                             FStarC_Syntax_Syntax.args =
                                               s_args
                                           }) in
                                    let uu___9 =
                                      mk
                                        (FStarC_Syntax_Syntax.Tm_app
                                           {
                                             FStarC_Syntax_Syntax.hd = u_head;
                                             FStarC_Syntax_Syntax.args =
                                               u_args1
                                           }) in
                                    (final_type1, uu___8, uu___9)))))))
      | FStarC_Syntax_Syntax.Tm_let
          { FStarC_Syntax_Syntax.lbs = (false, binding::[]);
            FStarC_Syntax_Syntax.body1 = e2;_}
          -> mk_let env1 binding e2 infer check_m
      | FStarC_Syntax_Syntax.Tm_match
          { FStarC_Syntax_Syntax.scrutinee = e0;
            FStarC_Syntax_Syntax.ret_opt = uu___1;
            FStarC_Syntax_Syntax.brs = branches;
            FStarC_Syntax_Syntax.rc_opt1 = uu___2;_}
          -> mk_match env1 e0 branches infer
      | FStarC_Syntax_Syntax.Tm_uinst (e1, uu___1) -> infer env1 e1
      | FStarC_Syntax_Syntax.Tm_meta
          { FStarC_Syntax_Syntax.tm2 = e1;
            FStarC_Syntax_Syntax.meta = uu___1;_}
          -> infer env1 e1
      | FStarC_Syntax_Syntax.Tm_ascribed
          { FStarC_Syntax_Syntax.tm = e1; FStarC_Syntax_Syntax.asc = uu___1;
            FStarC_Syntax_Syntax.eff_opt = uu___2;_}
          -> infer env1 e1
      | FStarC_Syntax_Syntax.Tm_constant c ->
          let uu___1 = let uu___2 = env1.tc_const c in N uu___2 in
          (uu___1, e, e)
      | FStarC_Syntax_Syntax.Tm_quoted (tm, qt) ->
          ((N FStarC_Syntax_Syntax.t_term), e, e)
      | FStarC_Syntax_Syntax.Tm_let uu___1 ->
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
            FStarC_Compiler_Util.format1 "[infer]: Tm_let %s" uu___3 in
          failwith uu___2
      | FStarC_Syntax_Syntax.Tm_type uu___1 ->
          failwith "impossible (DM stratification)"
      | FStarC_Syntax_Syntax.Tm_arrow uu___1 ->
          failwith "impossible (DM stratification)"
      | FStarC_Syntax_Syntax.Tm_refine uu___1 ->
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
            FStarC_Compiler_Util.format1 "[infer]: Tm_refine %s" uu___3 in
          failwith uu___2
      | FStarC_Syntax_Syntax.Tm_uvar uu___1 ->
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
            FStarC_Compiler_Util.format1 "[infer]: Tm_uvar %s" uu___3 in
          failwith uu___2
      | FStarC_Syntax_Syntax.Tm_delayed uu___1 ->
          failwith "impossible (compressed)"
      | FStarC_Syntax_Syntax.Tm_unknown ->
          let uu___1 =
            let uu___2 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
            FStarC_Compiler_Util.format1 "[infer]: Tm_unknown %s" uu___2 in
          failwith uu___1
and (mk_match :
  env ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      (FStarC_Syntax_Syntax.pat' FStarC_Syntax_Syntax.withinfo_t *
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStarC_Syntax_Syntax.term'
        FStarC_Syntax_Syntax.syntax) Prims.list ->
        (env ->
           FStarC_Syntax_Syntax.term ->
             (nm * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term))
          -> (nm * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e0 ->
      fun branches ->
        fun f ->
          let mk x = FStarC_Syntax_Syntax.mk x e0.FStarC_Syntax_Syntax.pos in
          let uu___ = check_n env1 e0 in
          match uu___ with
          | (uu___1, s_e0, u_e0) ->
              let uu___2 =
                let uu___3 =
                  FStarC_Compiler_List.map
                    (fun b ->
                       let uu___4 = FStarC_Syntax_Subst.open_branch b in
                       match uu___4 with
                       | (pat, FStar_Pervasives_Native.None, body) ->
                           let env2 =
                             let uu___5 =
                               let uu___6 = FStarC_Syntax_Syntax.pat_bvs pat in
                               FStarC_Compiler_List.fold_left
                                 FStarC_TypeChecker_Env.push_bv env1.tcenv
                                 uu___6 in
                             {
                               tcenv = uu___5;
                               subst = (env1.subst);
                               tc_const = (env1.tc_const)
                             } in
                           let uu___5 = f env2 body in
                           (match uu___5 with
                            | (nm1, s_body, u_body) ->
                                (nm1,
                                  (pat, FStar_Pervasives_Native.None,
                                    (s_body, u_body, body))))
                       | uu___5 ->
                           FStarC_Errors.raise_error0
                             FStarC_Errors_Codes.Fatal_WhenClauseNotSupported
                             ()
                             (Obj.magic
                                FStarC_Errors_Msg.is_error_message_string)
                             (Obj.magic
                                "No when clauses in the definition language"))
                    branches in
                FStarC_Compiler_List.split uu___3 in
              (match uu___2 with
               | (nms, branches1) ->
                   let t1 =
                     let uu___3 = FStarC_Compiler_List.hd nms in
                     match uu___3 with | M t11 -> t11 | N t11 -> t11 in
                   let has_m =
                     FStarC_Compiler_List.existsb
                       (fun uu___3 ->
                          match uu___3 with
                          | M uu___4 -> true
                          | uu___4 -> false) nms in
                   let uu___3 =
                     let uu___4 =
                       FStarC_Compiler_List.map2
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
                     FStarC_Compiler_List.unzip3 uu___4 in
                   (match uu___3 with
                    | (nms1, s_branches, u_branches) ->
                        if has_m
                        then
                          let p_type = mk_star_to_type mk env1 t1 in
                          let p =
                            FStarC_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_branches1 =
                            FStarC_Compiler_List.map
                              (fun uu___4 ->
                                 match uu___4 with
                                 | (pat, guard, s_body) ->
                                     let s_body1 =
                                       let uu___5 =
                                         let uu___6 =
                                           let uu___7 =
                                             let uu___8 =
                                               let uu___9 =
                                                 FStarC_Syntax_Syntax.bv_to_name
                                                   p in
                                               let uu___10 =
                                                 FStarC_Syntax_Syntax.as_aqual_implicit
                                                   false in
                                               (uu___9, uu___10) in
                                             [uu___8] in
                                           {
                                             FStarC_Syntax_Syntax.hd = s_body;
                                             FStarC_Syntax_Syntax.args =
                                               uu___7
                                           } in
                                         FStarC_Syntax_Syntax.Tm_app uu___6 in
                                       mk uu___5 in
                                     (pat, guard, s_body1)) s_branches in
                          let s_branches2 =
                            FStarC_Compiler_List.map
                              FStarC_Syntax_Subst.close_branch s_branches1 in
                          let u_branches1 =
                            FStarC_Compiler_List.map
                              FStarC_Syntax_Subst.close_branch u_branches in
                          let s_e =
                            let uu___4 =
                              let uu___5 = FStarC_Syntax_Syntax.mk_binder p in
                              [uu___5] in
                            let uu___5 =
                              mk
                                (FStarC_Syntax_Syntax.Tm_match
                                   {
                                     FStarC_Syntax_Syntax.scrutinee = s_e0;
                                     FStarC_Syntax_Syntax.ret_opt =
                                       FStar_Pervasives_Native.None;
                                     FStarC_Syntax_Syntax.brs = s_branches2;
                                     FStarC_Syntax_Syntax.rc_opt1 =
                                       FStar_Pervasives_Native.None
                                   }) in
                            FStarC_Syntax_Util.abs uu___4 uu___5
                              (FStar_Pervasives_Native.Some
                                 (FStarC_Syntax_Util.residual_tot
                                    FStarC_Syntax_Util.ktype0)) in
                          let t1_star =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  FStarC_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None p_type in
                                FStarC_Syntax_Syntax.mk_binder uu___6 in
                              [uu___5] in
                            let uu___5 =
                              FStarC_Syntax_Syntax.mk_Total
                                FStarC_Syntax_Util.ktype0 in
                            FStarC_Syntax_Util.arrow uu___4 uu___5 in
                          let uu___4 =
                            mk
                              (FStarC_Syntax_Syntax.Tm_ascribed
                                 {
                                   FStarC_Syntax_Syntax.tm = s_e;
                                   FStarC_Syntax_Syntax.asc =
                                     ((FStar_Pervasives.Inl t1_star),
                                       FStar_Pervasives_Native.None, false);
                                   FStarC_Syntax_Syntax.eff_opt =
                                     FStar_Pervasives_Native.None
                                 }) in
                          let uu___5 =
                            mk
                              (FStarC_Syntax_Syntax.Tm_match
                                 {
                                   FStarC_Syntax_Syntax.scrutinee = u_e0;
                                   FStarC_Syntax_Syntax.ret_opt =
                                     FStar_Pervasives_Native.None;
                                   FStarC_Syntax_Syntax.brs = u_branches1;
                                   FStarC_Syntax_Syntax.rc_opt1 =
                                     FStar_Pervasives_Native.None
                                 }) in
                          ((M t1), uu___4, uu___5)
                        else
                          (let s_branches1 =
                             FStarC_Compiler_List.map
                               FStarC_Syntax_Subst.close_branch s_branches in
                           let u_branches1 =
                             FStarC_Compiler_List.map
                               FStarC_Syntax_Subst.close_branch u_branches in
                           let t1_star = t1 in
                           let uu___5 =
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   mk
                                     (FStarC_Syntax_Syntax.Tm_match
                                        {
                                          FStarC_Syntax_Syntax.scrutinee =
                                            s_e0;
                                          FStarC_Syntax_Syntax.ret_opt =
                                            FStar_Pervasives_Native.None;
                                          FStarC_Syntax_Syntax.brs =
                                            s_branches1;
                                          FStarC_Syntax_Syntax.rc_opt1 =
                                            FStar_Pervasives_Native.None
                                        }) in
                                 {
                                   FStarC_Syntax_Syntax.tm = uu___8;
                                   FStarC_Syntax_Syntax.asc =
                                     ((FStar_Pervasives.Inl t1_star),
                                       FStar_Pervasives_Native.None, false);
                                   FStarC_Syntax_Syntax.eff_opt =
                                     FStar_Pervasives_Native.None
                                 } in
                               FStarC_Syntax_Syntax.Tm_ascribed uu___7 in
                             mk uu___6 in
                           let uu___6 =
                             mk
                               (FStarC_Syntax_Syntax.Tm_match
                                  {
                                    FStarC_Syntax_Syntax.scrutinee = u_e0;
                                    FStarC_Syntax_Syntax.ret_opt =
                                      FStar_Pervasives_Native.None;
                                    FStarC_Syntax_Syntax.brs = u_branches1;
                                    FStarC_Syntax_Syntax.rc_opt1 =
                                      FStar_Pervasives_Native.None
                                  }) in
                           ((N t1), uu___5, uu___6))))
and (mk_let :
  env_ ->
    FStarC_Syntax_Syntax.letbinding ->
      FStarC_Syntax_Syntax.term ->
        (env_ ->
           FStarC_Syntax_Syntax.term ->
             (nm * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term))
          ->
          (env_ ->
             FStarC_Syntax_Syntax.term ->
               (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
                 FStarC_Syntax_Syntax.term))
            -> (nm * FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term))
  =
  fun env1 ->
    fun binding ->
      fun e2 ->
        fun proceed ->
          fun ensure_m ->
            let mk x = FStarC_Syntax_Syntax.mk x e2.FStarC_Syntax_Syntax.pos in
            let e1 = binding.FStarC_Syntax_Syntax.lbdef in
            let x =
              FStarC_Compiler_Util.left binding.FStarC_Syntax_Syntax.lbname in
            let x_binders =
              let uu___ = FStarC_Syntax_Syntax.mk_binder x in [uu___] in
            let uu___ = FStarC_Syntax_Subst.open_term x_binders e2 in
            match uu___ with
            | (x_binders1, e21) ->
                let uu___1 = infer env1 e1 in
                (match uu___1 with
                 | (N t1, s_e1, u_e1) ->
                     let u_binding =
                       let uu___2 = is_C t1 in
                       if uu___2
                       then
                         let uu___3 =
                           let uu___4 =
                             FStarC_Syntax_Subst.subst env1.subst s_e1 in
                           trans_F_ env1 t1 uu___4 in
                         {
                           FStarC_Syntax_Syntax.lbname =
                             (binding.FStarC_Syntax_Syntax.lbname);
                           FStarC_Syntax_Syntax.lbunivs =
                             (binding.FStarC_Syntax_Syntax.lbunivs);
                           FStarC_Syntax_Syntax.lbtyp = uu___3;
                           FStarC_Syntax_Syntax.lbeff =
                             (binding.FStarC_Syntax_Syntax.lbeff);
                           FStarC_Syntax_Syntax.lbdef =
                             (binding.FStarC_Syntax_Syntax.lbdef);
                           FStarC_Syntax_Syntax.lbattrs =
                             (binding.FStarC_Syntax_Syntax.lbattrs);
                           FStarC_Syntax_Syntax.lbpos =
                             (binding.FStarC_Syntax_Syntax.lbpos)
                         }
                       else binding in
                     let env2 =
                       let uu___2 =
                         FStarC_TypeChecker_Env.push_bv env1.tcenv
                           {
                             FStarC_Syntax_Syntax.ppname =
                               (x.FStarC_Syntax_Syntax.ppname);
                             FStarC_Syntax_Syntax.index =
                               (x.FStarC_Syntax_Syntax.index);
                             FStarC_Syntax_Syntax.sort = t1
                           } in
                       {
                         tcenv = uu___2;
                         subst = (env1.subst);
                         tc_const = (env1.tc_const)
                       } in
                     let uu___2 = proceed env2 e21 in
                     (match uu___2 with
                      | (nm_rec, s_e2, u_e2) ->
                          let s_binding =
                            let uu___3 =
                              star_type' env2
                                binding.FStarC_Syntax_Syntax.lbtyp in
                            {
                              FStarC_Syntax_Syntax.lbname =
                                (binding.FStarC_Syntax_Syntax.lbname);
                              FStarC_Syntax_Syntax.lbunivs =
                                (binding.FStarC_Syntax_Syntax.lbunivs);
                              FStarC_Syntax_Syntax.lbtyp = uu___3;
                              FStarC_Syntax_Syntax.lbeff =
                                (binding.FStarC_Syntax_Syntax.lbeff);
                              FStarC_Syntax_Syntax.lbdef =
                                (binding.FStarC_Syntax_Syntax.lbdef);
                              FStarC_Syntax_Syntax.lbattrs =
                                (binding.FStarC_Syntax_Syntax.lbattrs);
                              FStarC_Syntax_Syntax.lbpos =
                                (binding.FStarC_Syntax_Syntax.lbpos)
                            } in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  FStarC_Syntax_Subst.close x_binders1 s_e2 in
                                {
                                  FStarC_Syntax_Syntax.lbs =
                                    (false,
                                      [{
                                         FStarC_Syntax_Syntax.lbname =
                                           (s_binding.FStarC_Syntax_Syntax.lbname);
                                         FStarC_Syntax_Syntax.lbunivs =
                                           (s_binding.FStarC_Syntax_Syntax.lbunivs);
                                         FStarC_Syntax_Syntax.lbtyp =
                                           (s_binding.FStarC_Syntax_Syntax.lbtyp);
                                         FStarC_Syntax_Syntax.lbeff =
                                           (s_binding.FStarC_Syntax_Syntax.lbeff);
                                         FStarC_Syntax_Syntax.lbdef = s_e1;
                                         FStarC_Syntax_Syntax.lbattrs =
                                           (s_binding.FStarC_Syntax_Syntax.lbattrs);
                                         FStarC_Syntax_Syntax.lbpos =
                                           (s_binding.FStarC_Syntax_Syntax.lbpos)
                                       }]);
                                  FStarC_Syntax_Syntax.body1 = uu___6
                                } in
                              FStarC_Syntax_Syntax.Tm_let uu___5 in
                            mk uu___4 in
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStarC_Syntax_Subst.close x_binders1 u_e2 in
                                {
                                  FStarC_Syntax_Syntax.lbs =
                                    (false,
                                      [{
                                         FStarC_Syntax_Syntax.lbname =
                                           (u_binding.FStarC_Syntax_Syntax.lbname);
                                         FStarC_Syntax_Syntax.lbunivs =
                                           (u_binding.FStarC_Syntax_Syntax.lbunivs);
                                         FStarC_Syntax_Syntax.lbtyp =
                                           (u_binding.FStarC_Syntax_Syntax.lbtyp);
                                         FStarC_Syntax_Syntax.lbeff =
                                           (u_binding.FStarC_Syntax_Syntax.lbeff);
                                         FStarC_Syntax_Syntax.lbdef = u_e1;
                                         FStarC_Syntax_Syntax.lbattrs =
                                           (u_binding.FStarC_Syntax_Syntax.lbattrs);
                                         FStarC_Syntax_Syntax.lbpos =
                                           (u_binding.FStarC_Syntax_Syntax.lbpos)
                                       }]);
                                  FStarC_Syntax_Syntax.body1 = uu___7
                                } in
                              FStarC_Syntax_Syntax.Tm_let uu___6 in
                            mk uu___5 in
                          (nm_rec, uu___3, uu___4))
                 | (M t1, s_e1, u_e1) ->
                     let u_binding =
                       {
                         FStarC_Syntax_Syntax.lbname =
                           (binding.FStarC_Syntax_Syntax.lbname);
                         FStarC_Syntax_Syntax.lbunivs =
                           (binding.FStarC_Syntax_Syntax.lbunivs);
                         FStarC_Syntax_Syntax.lbtyp = t1;
                         FStarC_Syntax_Syntax.lbeff =
                           FStarC_Parser_Const.effect_PURE_lid;
                         FStarC_Syntax_Syntax.lbdef =
                           (binding.FStarC_Syntax_Syntax.lbdef);
                         FStarC_Syntax_Syntax.lbattrs =
                           (binding.FStarC_Syntax_Syntax.lbattrs);
                         FStarC_Syntax_Syntax.lbpos =
                           (binding.FStarC_Syntax_Syntax.lbpos)
                       } in
                     let env2 =
                       let uu___2 =
                         FStarC_TypeChecker_Env.push_bv env1.tcenv
                           {
                             FStarC_Syntax_Syntax.ppname =
                               (x.FStarC_Syntax_Syntax.ppname);
                             FStarC_Syntax_Syntax.index =
                               (x.FStarC_Syntax_Syntax.index);
                             FStarC_Syntax_Syntax.sort = t1
                           } in
                       {
                         tcenv = uu___2;
                         subst = (env1.subst);
                         tc_const = (env1.tc_const)
                       } in
                     let uu___2 = ensure_m env2 e21 in
                     (match uu___2 with
                      | (t2, s_e2, u_e2) ->
                          let p_type = mk_star_to_type mk env2 t2 in
                          let p =
                            FStarC_Syntax_Syntax.gen_bv "p''"
                              FStar_Pervasives_Native.None p_type in
                          let s_e21 =
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 =
                                      FStarC_Syntax_Syntax.bv_to_name p in
                                    let uu___8 =
                                      FStarC_Syntax_Syntax.as_aqual_implicit
                                        false in
                                    (uu___7, uu___8) in
                                  [uu___6] in
                                {
                                  FStarC_Syntax_Syntax.hd = s_e2;
                                  FStarC_Syntax_Syntax.args = uu___5
                                } in
                              FStarC_Syntax_Syntax.Tm_app uu___4 in
                            mk uu___3 in
                          let s_e22 =
                            FStarC_Syntax_Util.abs x_binders1 s_e21
                              (FStar_Pervasives_Native.Some
                                 (FStarC_Syntax_Util.residual_tot
                                    FStarC_Syntax_Util.ktype0)) in
                          let body =
                            let uu___3 =
                              let uu___4 =
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 =
                                      FStarC_Syntax_Syntax.as_aqual_implicit
                                        false in
                                    (s_e22, uu___7) in
                                  [uu___6] in
                                {
                                  FStarC_Syntax_Syntax.hd = s_e1;
                                  FStarC_Syntax_Syntax.args = uu___5
                                } in
                              FStarC_Syntax_Syntax.Tm_app uu___4 in
                            mk uu___3 in
                          let uu___3 =
                            let uu___4 =
                              let uu___5 = FStarC_Syntax_Syntax.mk_binder p in
                              [uu___5] in
                            FStarC_Syntax_Util.abs uu___4 body
                              (FStar_Pervasives_Native.Some
                                 (FStarC_Syntax_Util.residual_tot
                                    FStarC_Syntax_Util.ktype0)) in
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStarC_Syntax_Subst.close x_binders1 u_e2 in
                                {
                                  FStarC_Syntax_Syntax.lbs =
                                    (false,
                                      [{
                                         FStarC_Syntax_Syntax.lbname =
                                           (u_binding.FStarC_Syntax_Syntax.lbname);
                                         FStarC_Syntax_Syntax.lbunivs =
                                           (u_binding.FStarC_Syntax_Syntax.lbunivs);
                                         FStarC_Syntax_Syntax.lbtyp =
                                           (u_binding.FStarC_Syntax_Syntax.lbtyp);
                                         FStarC_Syntax_Syntax.lbeff =
                                           (u_binding.FStarC_Syntax_Syntax.lbeff);
                                         FStarC_Syntax_Syntax.lbdef = u_e1;
                                         FStarC_Syntax_Syntax.lbattrs =
                                           (u_binding.FStarC_Syntax_Syntax.lbattrs);
                                         FStarC_Syntax_Syntax.lbpos =
                                           (u_binding.FStarC_Syntax_Syntax.lbpos)
                                       }]);
                                  FStarC_Syntax_Syntax.body1 = uu___7
                                } in
                              FStarC_Syntax_Syntax.Tm_let uu___6 in
                            mk uu___5 in
                          ((M t2), uu___3, uu___4)))
and (check_n :
  env_ ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.term *
        FStarC_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mn =
        let uu___ =
          FStarC_Syntax_Syntax.mk FStarC_Syntax_Syntax.Tm_unknown
            e.FStarC_Syntax_Syntax.pos in
        N uu___ in
      let uu___ = check env1 e mn in
      match uu___ with
      | (N t, s_e, u_e) -> (t, s_e, u_e)
      | uu___1 -> failwith "[check_n]: impossible"
and (check_m :
  env_ ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.term *
        FStarC_Syntax_Syntax.term))
  =
  fun env1 ->
    fun e ->
      let mn =
        let uu___ =
          FStarC_Syntax_Syntax.mk FStarC_Syntax_Syntax.Tm_unknown
            e.FStarC_Syntax_Syntax.pos in
        M uu___ in
      let uu___ = check env1 e mn in
      match uu___ with
      | (M t, s_e, u_e) -> (t, s_e, u_e)
      | uu___1 -> failwith "[check_m]: impossible"
and (comp_of_nm : nm_ -> FStarC_Syntax_Syntax.comp) =
  fun nm1 ->
    match nm1 with | N t -> FStarC_Syntax_Syntax.mk_Total t | M t -> mk_M t
and (mk_M : FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.comp) =
  fun t ->
    FStarC_Syntax_Syntax.mk_Comp
      {
        FStarC_Syntax_Syntax.comp_univs = [FStarC_Syntax_Syntax.U_unknown];
        FStarC_Syntax_Syntax.effect_name = FStarC_Parser_Const.monadic_lid;
        FStarC_Syntax_Syntax.result_typ = t;
        FStarC_Syntax_Syntax.effect_args = [];
        FStarC_Syntax_Syntax.flags =
          [FStarC_Syntax_Syntax.CPS; FStarC_Syntax_Syntax.TOTAL]
      }
and (type_of_comp :
  FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  = fun t -> FStarC_Syntax_Util.comp_result t
and (trans_F_ :
  env_ ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun wp ->
        (let uu___1 = let uu___2 = is_C c in Prims.op_Negation uu___2 in
         if uu___1
         then
           let uu___2 =
             let uu___3 =
               FStarC_Class_Show.show FStarC_Syntax_Print.showable_term c in
             FStarC_Compiler_Util.format1 "Not a DM4F C-type: %s" uu___3 in
           FStarC_Errors.raise_error
             (FStarC_Syntax_Syntax.has_range_syntax ()) c
             FStarC_Errors_Codes.Error_UnexpectedDM4FType ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_string)
             (Obj.magic uu___2)
         else ());
        (let mk x = FStarC_Syntax_Syntax.mk x c.FStarC_Syntax_Syntax.pos in
         let uu___1 =
           let uu___2 = FStarC_Syntax_Subst.compress c in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_app
             { FStarC_Syntax_Syntax.hd = head;
               FStarC_Syntax_Syntax.args = args;_}
             ->
             let uu___2 = FStarC_Syntax_Util.head_and_args wp in
             (match uu___2 with
              | (wp_head, wp_args) ->
                  ((let uu___4 =
                      (Prims.op_Negation
                         ((FStarC_Compiler_List.length wp_args) =
                            (FStarC_Compiler_List.length args)))
                        ||
                        (let uu___5 =
                           let uu___6 =
                             FStarC_Parser_Const.mk_tuple_data_lid
                               (FStarC_Compiler_List.length wp_args)
                               FStarC_Compiler_Range_Type.dummyRange in
                           FStarC_Syntax_Util.is_constructor wp_head uu___6 in
                         Prims.op_Negation uu___5) in
                    if uu___4 then failwith "mismatch" else ());
                   (let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          FStarC_Compiler_List.map2
                            (fun uu___7 ->
                               fun uu___8 ->
                                 match (uu___7, uu___8) with
                                 | ((arg, q), (wp_arg, q')) ->
                                     let print_implicit q1 =
                                       let uu___9 =
                                         FStarC_Syntax_Syntax.is_aqual_implicit
                                           q1 in
                                       if uu___9
                                       then "implicit"
                                       else "explicit" in
                                     ((let uu___10 =
                                         let uu___11 =
                                           FStarC_Syntax_Util.eq_aqual q q' in
                                         Prims.op_Negation uu___11 in
                                       if uu___10
                                       then
                                         let uu___11 =
                                           let uu___12 = print_implicit q in
                                           let uu___13 = print_implicit q' in
                                           FStarC_Compiler_Util.format2
                                             "Incoherent implicit qualifiers %s %s\n"
                                             uu___12 uu___13 in
                                         FStarC_Errors.log_issue
                                           FStarC_Class_HasRange.hasRange_range
                                           head.FStarC_Syntax_Syntax.pos
                                           FStarC_Errors_Codes.Warning_IncoherentImplicitQualifier
                                           ()
                                           (Obj.magic
                                              FStarC_Errors_Msg.is_error_message_string)
                                           (Obj.magic uu___11)
                                       else ());
                                      (let uu___10 = trans_F_ env1 arg wp_arg in
                                       (uu___10, q)))) args wp_args in
                        {
                          FStarC_Syntax_Syntax.hd = head;
                          FStarC_Syntax_Syntax.args = uu___6
                        } in
                      FStarC_Syntax_Syntax.Tm_app uu___5 in
                    mk uu___4)))
         | FStarC_Syntax_Syntax.Tm_arrow
             { FStarC_Syntax_Syntax.bs1 = binders;
               FStarC_Syntax_Syntax.comp = comp;_}
             ->
             let binders1 = FStarC_Syntax_Util.name_binders binders in
             let uu___2 = FStarC_Syntax_Subst.open_comp binders1 comp in
             (match uu___2 with
              | (binders_orig, comp1) ->
                  let uu___3 =
                    let uu___4 =
                      FStarC_Compiler_List.map
                        (fun b ->
                           let uu___5 =
                             ((b.FStarC_Syntax_Syntax.binder_bv),
                               (b.FStarC_Syntax_Syntax.binder_qual)) in
                           match uu___5 with
                           | (bv, q) ->
                               let h = bv.FStarC_Syntax_Syntax.sort in
                               let uu___6 = is_C h in
                               if uu___6
                               then
                                 let w' =
                                   let uu___7 =
                                     let uu___8 =
                                       FStarC_Ident.string_of_id
                                         bv.FStarC_Syntax_Syntax.ppname in
                                     Prims.strcat uu___8 "__w'" in
                                   let uu___8 = star_type' env1 h in
                                   FStarC_Syntax_Syntax.gen_bv uu___7
                                     FStar_Pervasives_Native.None uu___8 in
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           let uu___12 =
                                             FStarC_Syntax_Syntax.bv_to_name
                                               w' in
                                           trans_F_ env1 h uu___12 in
                                         FStarC_Syntax_Syntax.null_bv uu___11 in
                                       {
                                         FStarC_Syntax_Syntax.binder_bv =
                                           uu___10;
                                         FStarC_Syntax_Syntax.binder_qual =
                                           (b.FStarC_Syntax_Syntax.binder_qual);
                                         FStarC_Syntax_Syntax.binder_positivity
                                           =
                                           (b.FStarC_Syntax_Syntax.binder_positivity);
                                         FStarC_Syntax_Syntax.binder_attrs =
                                           (b.FStarC_Syntax_Syntax.binder_attrs)
                                       } in
                                     [uu___9] in
                                   {
                                     FStarC_Syntax_Syntax.binder_bv = w';
                                     FStarC_Syntax_Syntax.binder_qual =
                                       (b.FStarC_Syntax_Syntax.binder_qual);
                                     FStarC_Syntax_Syntax.binder_positivity =
                                       (b.FStarC_Syntax_Syntax.binder_positivity);
                                     FStarC_Syntax_Syntax.binder_attrs =
                                       (b.FStarC_Syntax_Syntax.binder_attrs)
                                   } :: uu___8 in
                                 (w', uu___7)
                               else
                                 (let x =
                                    let uu___8 =
                                      let uu___9 =
                                        FStarC_Ident.string_of_id
                                          bv.FStarC_Syntax_Syntax.ppname in
                                      Prims.strcat uu___9 "__x" in
                                    let uu___9 = star_type' env1 h in
                                    FStarC_Syntax_Syntax.gen_bv uu___8
                                      FStar_Pervasives_Native.None uu___9 in
                                  (x,
                                    [{
                                       FStarC_Syntax_Syntax.binder_bv = x;
                                       FStarC_Syntax_Syntax.binder_qual =
                                         (b.FStarC_Syntax_Syntax.binder_qual);
                                       FStarC_Syntax_Syntax.binder_positivity
                                         =
                                         (b.FStarC_Syntax_Syntax.binder_positivity);
                                       FStarC_Syntax_Syntax.binder_attrs =
                                         (b.FStarC_Syntax_Syntax.binder_attrs)
                                     }]))) binders_orig in
                    FStarC_Compiler_List.split uu___4 in
                  (match uu___3 with
                   | (bvs, binders2) ->
                       let binders3 = FStarC_Compiler_List.flatten binders2 in
                       let comp2 =
                         let uu___4 =
                           let uu___5 =
                             FStarC_Syntax_Syntax.binders_of_list bvs in
                           FStarC_Syntax_Util.rename_binders binders_orig
                             uu___5 in
                         FStarC_Syntax_Subst.subst_comp uu___4 comp1 in
                       let app =
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               FStarC_Compiler_List.map
                                 (fun bv ->
                                    let uu___7 =
                                      FStarC_Syntax_Syntax.bv_to_name bv in
                                    let uu___8 =
                                      FStarC_Syntax_Syntax.as_aqual_implicit
                                        false in
                                    (uu___7, uu___8)) bvs in
                             {
                               FStarC_Syntax_Syntax.hd = wp;
                               FStarC_Syntax_Syntax.args = uu___6
                             } in
                           FStarC_Syntax_Syntax.Tm_app uu___5 in
                         mk uu___4 in
                       let comp3 =
                         let uu___4 = type_of_comp comp2 in
                         let uu___5 = is_monadic_comp comp2 in
                         trans_G env1 uu___4 uu___5 app in
                       FStarC_Syntax_Util.arrow binders3 comp3))
         | FStarC_Syntax_Syntax.Tm_ascribed
             { FStarC_Syntax_Syntax.tm = e;
               FStarC_Syntax_Syntax.asc = uu___2;
               FStarC_Syntax_Syntax.eff_opt = uu___3;_}
             -> trans_F_ env1 e wp
         | uu___2 -> failwith "impossible trans_F_")
and (trans_G :
  env_ ->
    FStarC_Syntax_Syntax.typ ->
      Prims.bool -> FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.comp)
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
                  let uu___4 = FStarC_Syntax_Syntax.as_aqual_implicit false in
                  (wp, uu___4) in
                [uu___3] in
              {
                FStarC_Syntax_Syntax.comp_univs =
                  [FStarC_Syntax_Syntax.U_unknown];
                FStarC_Syntax_Syntax.effect_name =
                  FStarC_Parser_Const.effect_PURE_lid;
                FStarC_Syntax_Syntax.result_typ = uu___1;
                FStarC_Syntax_Syntax.effect_args = uu___2;
                FStarC_Syntax_Syntax.flags = []
              } in
            FStarC_Syntax_Syntax.mk_Comp uu___
          else
            (let uu___1 = trans_F_ env1 h wp in
             FStarC_Syntax_Syntax.mk_Total uu___1)
let (n :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  FStarC_TypeChecker_Normalize.normalize
    [FStarC_TypeChecker_Env.DontUnfoldAttr
       [FStarC_Parser_Const.tac_opaque_attr];
    FStarC_TypeChecker_Env.Beta;
    FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
    FStarC_TypeChecker_Env.DoNotUnfoldPureLets;
    FStarC_TypeChecker_Env.Eager_unfolding;
    FStarC_TypeChecker_Env.EraseUniverses]
let (star_type : env -> FStarC_Syntax_Syntax.typ -> FStarC_Syntax_Syntax.typ)
  = fun env1 -> fun t -> let uu___ = n env1.tcenv t in star_type' env1 uu___
let (star_expr :
  env ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Syntax_Syntax.typ * FStarC_Syntax_Syntax.term *
        FStarC_Syntax_Syntax.term))
  = fun env1 -> fun t -> let uu___ = n env1.tcenv t in check_n env1 uu___
let (trans_F :
  env ->
    FStarC_Syntax_Syntax.typ ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun env1 ->
    fun c ->
      fun wp ->
        let uu___ = n env1.tcenv c in
        let uu___1 = n env1.tcenv wp in trans_F_ env1 uu___ uu___1
let (recheck_debug :
  Prims.string ->
    FStarC_TypeChecker_Env.env ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun s ->
    fun env1 ->
      fun t ->
        (let uu___1 = FStarC_Compiler_Effect.op_Bang dbg in
         if uu___1
         then
           let uu___2 =
             FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
           FStarC_Compiler_Util.print2
             "Term has been %s-transformed to:\n%s\n----------\n" s uu___2
         else ());
        (let uu___1 = FStarC_TypeChecker_TcTerm.tc_term env1 t in
         match uu___1 with
         | (t', uu___2, uu___3) ->
             ((let uu___5 = FStarC_Compiler_Effect.op_Bang dbg in
               if uu___5
               then
                 let uu___6 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     t' in
                 FStarC_Compiler_Util.print1
                   "Re-checked; got:\n%s\n----------\n" uu___6
               else ());
              t'))
let (cps_and_elaborate :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.eff_decl ->
      (FStarC_Syntax_Syntax.sigelt Prims.list * FStarC_Syntax_Syntax.eff_decl
        * FStarC_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  =
  fun env1 ->
    fun ed ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Syntax_Util.effect_sig_ts
              ed.FStarC_Syntax_Syntax.signature in
          FStar_Pervasives_Native.snd uu___2 in
        FStarC_Syntax_Subst.open_term ed.FStarC_Syntax_Syntax.binders uu___1 in
      match uu___ with
      | (effect_binders_un, signature_un) ->
          let uu___1 =
            FStarC_TypeChecker_TcTerm.tc_tparams env1 effect_binders_un in
          (match uu___1 with
           | (effect_binders, env2, uu___2) ->
               let uu___3 =
                 FStarC_TypeChecker_TcTerm.tc_trivial_guard env2 signature_un in
               (match uu___3 with
                | (signature, uu___4) ->
                    let raise_error code msg =
                      FStarC_Errors.raise_error
                        FStarC_Class_HasRange.hasRange_range
                        signature.FStarC_Syntax_Syntax.pos code ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic msg) in
                    let effect_binders1 =
                      FStarC_Compiler_List.map
                        (fun b ->
                           let uu___5 =
                             let uu___6 = b.FStarC_Syntax_Syntax.binder_bv in
                             let uu___7 =
                               FStarC_TypeChecker_Normalize.normalize
                                 [FStarC_TypeChecker_Env.EraseUniverses] env2
                                 (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                             {
                               FStarC_Syntax_Syntax.ppname =
                                 (uu___6.FStarC_Syntax_Syntax.ppname);
                               FStarC_Syntax_Syntax.index =
                                 (uu___6.FStarC_Syntax_Syntax.index);
                               FStarC_Syntax_Syntax.sort = uu___7
                             } in
                           {
                             FStarC_Syntax_Syntax.binder_bv = uu___5;
                             FStarC_Syntax_Syntax.binder_qual =
                               (b.FStarC_Syntax_Syntax.binder_qual);
                             FStarC_Syntax_Syntax.binder_positivity =
                               (b.FStarC_Syntax_Syntax.binder_positivity);
                             FStarC_Syntax_Syntax.binder_attrs =
                               (b.FStarC_Syntax_Syntax.binder_attrs)
                           }) effect_binders in
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStarC_Syntax_Subst.compress signature_un in
                        uu___7.FStarC_Syntax_Syntax.n in
                      match uu___6 with
                      | FStarC_Syntax_Syntax.Tm_arrow
                          {
                            FStarC_Syntax_Syntax.bs1 =
                              { FStarC_Syntax_Syntax.binder_bv = a;
                                FStarC_Syntax_Syntax.binder_qual = uu___7;
                                FStarC_Syntax_Syntax.binder_positivity =
                                  uu___8;
                                FStarC_Syntax_Syntax.binder_attrs = uu___9;_}::[];
                            FStarC_Syntax_Syntax.comp = effect_marker;_}
                          -> (a, effect_marker)
                      | uu___7 ->
                          raise_error
                            FStarC_Errors_Codes.Fatal_BadSignatureShape
                            "bad shape for effect-for-free signature" in
                    (match uu___5 with
                     | (a, effect_marker) ->
                         let a1 =
                           let uu___6 = FStarC_Syntax_Syntax.is_null_bv a in
                           if uu___6
                           then
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Syntax_Syntax.range_of_bv a in
                               FStar_Pervasives_Native.Some uu___8 in
                             FStarC_Syntax_Syntax.gen_bv "a" uu___7
                               a.FStarC_Syntax_Syntax.sort
                           else a in
                         let open_and_check env3 other_binders t =
                           let subst =
                             FStarC_Syntax_Subst.opening_of_binders
                               (FStarC_Compiler_List.op_At effect_binders1
                                  other_binders) in
                           let t1 = FStarC_Syntax_Subst.subst subst t in
                           let uu___6 =
                             FStarC_TypeChecker_TcTerm.tc_term env3 t1 in
                           match uu___6 with
                           | (t2, comp, uu___7) -> (t2, comp) in
                         let mk x =
                           FStarC_Syntax_Syntax.mk x
                             signature.FStarC_Syntax_Syntax.pos in
                         let uu___6 =
                           let uu___7 =
                             let uu___8 =
                               let uu___9 =
                                 FStarC_Syntax_Util.get_eff_repr ed in
                               FStarC_Compiler_Util.must uu___9 in
                             FStar_Pervasives_Native.snd uu___8 in
                           open_and_check env2 [] uu___7 in
                         (match uu___6 with
                          | (repr, _comp) ->
                              ((let uu___8 =
                                  FStarC_Compiler_Effect.op_Bang dbg in
                                if uu___8
                                then
                                  let uu___9 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_term repr in
                                  FStarC_Compiler_Util.print1
                                    "Representation is: %s\n" uu___9
                                else ());
                               (let ed_range =
                                  FStarC_TypeChecker_Env.get_range env2 in
                                let dmff_env =
                                  empty env2
                                    (FStarC_TypeChecker_TcTerm.tc_constant
                                       env2
                                       FStarC_Compiler_Range_Type.dummyRange) in
                                let wp_type = star_type dmff_env repr in
                                let uu___8 = recheck_debug "*" env2 wp_type in
                                let wp_a =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              FStarC_Syntax_Syntax.bv_to_name
                                                a1 in
                                            let uu___15 =
                                              FStarC_Syntax_Syntax.as_aqual_implicit
                                                false in
                                            (uu___14, uu___15) in
                                          [uu___13] in
                                        {
                                          FStarC_Syntax_Syntax.hd = wp_type;
                                          FStarC_Syntax_Syntax.args = uu___12
                                        } in
                                      FStarC_Syntax_Syntax.Tm_app uu___11 in
                                    mk uu___10 in
                                  FStarC_TypeChecker_Normalize.normalize
                                    [FStarC_TypeChecker_Env.Beta] env2 uu___9 in
                                let effect_signature =
                                  let binders =
                                    let uu___9 =
                                      let uu___10 =
                                        FStarC_Syntax_Syntax.as_bqual_implicit
                                          false in
                                      FStarC_Syntax_Syntax.mk_binder_with_attrs
                                        a1 uu___10
                                        FStar_Pervasives_Native.None [] in
                                    let uu___10 =
                                      let uu___11 =
                                        let uu___12 =
                                          FStarC_Syntax_Syntax.gen_bv
                                            "dijkstra_wp"
                                            FStar_Pervasives_Native.None wp_a in
                                        FStarC_Syntax_Syntax.mk_binder
                                          uu___12 in
                                      [uu___11] in
                                    uu___9 :: uu___10 in
                                  let binders1 =
                                    FStarC_Syntax_Subst.close_binders binders in
                                  mk
                                    (FStarC_Syntax_Syntax.Tm_arrow
                                       {
                                         FStarC_Syntax_Syntax.bs1 = binders1;
                                         FStarC_Syntax_Syntax.comp =
                                           effect_marker
                                       }) in
                                let uu___9 =
                                  recheck_debug
                                    "turned into the effect signature" env2
                                    effect_signature in
                                let sigelts = FStarC_Compiler_Util.mk_ref [] in
                                let mk_lid name =
                                  FStarC_Syntax_Util.dm4f_lid ed name in
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
                                                 FStarC_TypeChecker_Common.is_total_lcomp
                                                   item_comp in
                                               Prims.op_Negation uu___14 in
                                             if uu___13
                                             then
                                               let uu___14 =
                                                 let uu___15 =
                                                   FStarC_Class_Show.show
                                                     FStarC_Syntax_Print.showable_term
                                                     item2 in
                                                 let uu___16 =
                                                   FStarC_TypeChecker_Common.lcomp_to_string
                                                     item_comp in
                                                 FStarC_Compiler_Util.format2
                                                   "Computation for [%s] is not total : %s !"
                                                   uu___15 uu___16 in
                                               FStarC_Errors.raise_error0
                                                 FStarC_Errors_Codes.Fatal_ComputationNotTotal
                                                 ()
                                                 (Obj.magic
                                                    FStarC_Errors_Msg.is_error_message_string)
                                                 (Obj.magic uu___14)
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
                                      FStarC_Syntax_Util.get_bind_repr ed in
                                    FStarC_Compiler_Util.must uu___12 in
                                  elaborate_and_star dmff_env [] uu___11 in
                                match uu___10 with
                                | (dmff_env1, uu___11, bind_wp, bind_elab) ->
                                    let uu___12 =
                                      let uu___13 =
                                        let uu___14 =
                                          FStarC_Syntax_Util.get_return_repr
                                            ed in
                                        FStarC_Compiler_Util.must uu___14 in
                                      elaborate_and_star dmff_env1 [] uu___13 in
                                    (match uu___12 with
                                     | (dmff_env2, uu___13, return_wp,
                                        return_elab) ->
                                         let rc_gtot =
                                           {
                                             FStarC_Syntax_Syntax.residual_effect
                                               =
                                               FStarC_Parser_Const.effect_GTot_lid;
                                             FStarC_Syntax_Syntax.residual_typ
                                               = FStar_Pervasives_Native.None;
                                             FStarC_Syntax_Syntax.residual_flags
                                               = []
                                           } in
                                         let lift_from_pure_wp =
                                           let uu___14 =
                                             let uu___15 =
                                               FStarC_Syntax_Subst.compress
                                                 return_wp in
                                             uu___15.FStarC_Syntax_Syntax.n in
                                           match uu___14 with
                                           | FStarC_Syntax_Syntax.Tm_abs
                                               {
                                                 FStarC_Syntax_Syntax.bs =
                                                   b1::b2::bs;
                                                 FStarC_Syntax_Syntax.body =
                                                   body;
                                                 FStarC_Syntax_Syntax.rc_opt
                                                   = what;_}
                                               ->
                                               let uu___15 =
                                                 let uu___16 =
                                                   let uu___17 =
                                                     FStarC_Syntax_Util.abs
                                                       bs body
                                                       FStar_Pervasives_Native.None in
                                                   FStarC_Syntax_Subst.open_term
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
                                                      FStarC_TypeChecker_Env.push_binders
                                                        uu___16 [b11; b21] in
                                                    let wp_b1 =
                                                      let raw_wp_b1 =
                                                        let uu___16 =
                                                          let uu___17 =
                                                            let uu___18 =
                                                              let uu___19 =
                                                                let uu___20 =
                                                                  FStarC_Syntax_Syntax.bv_to_name
                                                                    b11.FStarC_Syntax_Syntax.binder_bv in
                                                                let uu___21 =
                                                                  FStarC_Syntax_Syntax.as_aqual_implicit
                                                                    false in
                                                                (uu___20,
                                                                  uu___21) in
                                                              [uu___19] in
                                                            {
                                                              FStarC_Syntax_Syntax.hd
                                                                = wp_type;
                                                              FStarC_Syntax_Syntax.args
                                                                = uu___18
                                                            } in
                                                          FStarC_Syntax_Syntax.Tm_app
                                                            uu___17 in
                                                        mk uu___16 in
                                                      FStarC_TypeChecker_Normalize.normalize
                                                        [FStarC_TypeChecker_Env.Beta]
                                                        env0 raw_wp_b1 in
                                                    let uu___16 =
                                                      let uu___17 =
                                                        let uu___18 =
                                                          FStarC_Syntax_Util.unascribe
                                                            wp_b1 in
                                                        FStarC_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1 uu___18 in
                                                      FStarC_Syntax_Util.abs_formals
                                                        uu___17 in
                                                    (match uu___16 with
                                                     | (bs1, body2, what') ->
                                                         let fail uu___17 =
                                                           let error_msg =
                                                             let uu___18 =
                                                               FStarC_Class_Show.show
                                                                 FStarC_Syntax_Print.showable_term
                                                                 body2 in
                                                             let uu___19 =
                                                               match what'
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   -> "None"
                                                               | FStar_Pervasives_Native.Some
                                                                   rc ->
                                                                   FStarC_Ident.string_of_lid
                                                                    rc.FStarC_Syntax_Syntax.residual_effect in
                                                             FStarC_Compiler_Util.format2
                                                               "The body of return_wp (%s) should be of type Type0 but is of type %s"
                                                               uu___18
                                                               uu___19 in
                                                           raise_error
                                                             FStarC_Errors_Codes.Fatal_WrongBodyTypeForReturnWP
                                                             error_msg in
                                                         ((match what' with
                                                           | FStar_Pervasives_Native.None
                                                               -> fail ()
                                                           | FStar_Pervasives_Native.Some
                                                               rc ->
                                                               ((let uu___19
                                                                   =
                                                                   let uu___20
                                                                    =
                                                                    FStarC_Syntax_Util.is_pure_effect
                                                                    rc.FStarC_Syntax_Syntax.residual_effect in
                                                                   Prims.op_Negation
                                                                    uu___20 in
                                                                 if uu___19
                                                                 then fail ()
                                                                 else ());
                                                                (let uu___19
                                                                   =
                                                                   FStarC_Compiler_Util.map_opt
                                                                    rc.FStarC_Syntax_Syntax.residual_typ
                                                                    (fun rt
                                                                    ->
                                                                    let g_opt
                                                                    =
                                                                    FStarC_TypeChecker_Rel.try_teq
                                                                    true env2
                                                                    rt
                                                                    FStarC_Syntax_Util.ktype0 in
                                                                    match g_opt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    g' ->
                                                                    FStarC_TypeChecker_Rel.force_trivial_guard
                                                                    env2 g'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    fail ()) in
                                                                 ())));
                                                          (let wp =
                                                             let t2 =
                                                               (b21.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                             let pure_wp_type
                                                               =
                                                               double_star t2 in
                                                             FStarC_Syntax_Syntax.gen_bv
                                                               "wp"
                                                               FStar_Pervasives_Native.None
                                                               pure_wp_type in
                                                           let body3 =
                                                             let uu___18 =
                                                               FStarC_Syntax_Syntax.bv_to_name
                                                                 wp in
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 let uu___21
                                                                   =
                                                                   FStarC_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what' in
                                                                 (uu___21,
                                                                   FStar_Pervasives_Native.None) in
                                                               [uu___20] in
                                                             FStarC_Syntax_Syntax.mk_Tm_app
                                                               uu___18
                                                               uu___19
                                                               ed_range in
                                                           let uu___18 =
                                                             let uu___19 =
                                                               let uu___20 =
                                                                 FStarC_Syntax_Syntax.mk_binder
                                                                   wp in
                                                               [uu___20] in
                                                             b11 :: uu___19 in
                                                           let uu___19 =
                                                             FStarC_Syntax_Util.abs
                                                               bs1 body3 what in
                                                           FStarC_Syntax_Util.abs
                                                             uu___18 uu___19
                                                             (FStar_Pervasives_Native.Some
                                                                rc_gtot)))))
                                           | uu___15 ->
                                               raise_error
                                                 FStarC_Errors_Codes.Fatal_UnexpectedReturnShape
                                                 "unexpected shape for return" in
                                         let return_wp1 =
                                           let uu___14 =
                                             let uu___15 =
                                               FStarC_Syntax_Subst.compress
                                                 return_wp in
                                             uu___15.FStarC_Syntax_Syntax.n in
                                           match uu___14 with
                                           | FStarC_Syntax_Syntax.Tm_abs
                                               {
                                                 FStarC_Syntax_Syntax.bs =
                                                   b1::b2::bs;
                                                 FStarC_Syntax_Syntax.body =
                                                   body;
                                                 FStarC_Syntax_Syntax.rc_opt
                                                   = what;_}
                                               ->
                                               let uu___15 =
                                                 FStarC_Syntax_Util.abs bs
                                                   body what in
                                               FStarC_Syntax_Util.abs
                                                 [b1; b2] uu___15
                                                 (FStar_Pervasives_Native.Some
                                                    rc_gtot)
                                           | uu___15 ->
                                               raise_error
                                                 FStarC_Errors_Codes.Fatal_UnexpectedReturnShape
                                                 "unexpected shape for return" in
                                         let bind_wp1 =
                                           let uu___14 =
                                             let uu___15 =
                                               FStarC_Syntax_Subst.compress
                                                 bind_wp in
                                             uu___15.FStarC_Syntax_Syntax.n in
                                           match uu___14 with
                                           | FStarC_Syntax_Syntax.Tm_abs
                                               {
                                                 FStarC_Syntax_Syntax.bs =
                                                   binders;
                                                 FStarC_Syntax_Syntax.body =
                                                   body;
                                                 FStarC_Syntax_Syntax.rc_opt
                                                   = what;_}
                                               ->
                                               FStarC_Syntax_Util.abs binders
                                                 body what
                                           | uu___15 ->
                                               raise_error
                                                 FStarC_Errors_Codes.Fatal_UnexpectedBindShape
                                                 "unexpected shape for bind" in
                                         let apply_close t =
                                           if
                                             (FStarC_Compiler_List.length
                                                effect_binders1)
                                               = Prims.int_zero
                                           then t
                                           else
                                             (let uu___15 =
                                                let uu___16 =
                                                  let uu___17 =
                                                    let uu___18 =
                                                      let uu___19 =
                                                        FStarC_Syntax_Util.args_of_binders
                                                          effect_binders1 in
                                                      FStar_Pervasives_Native.snd
                                                        uu___19 in
                                                    {
                                                      FStarC_Syntax_Syntax.hd
                                                        = t;
                                                      FStarC_Syntax_Syntax.args
                                                        = uu___18
                                                    } in
                                                  FStarC_Syntax_Syntax.Tm_app
                                                    uu___17 in
                                                mk uu___16 in
                                              FStarC_Syntax_Subst.close
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
                                             FStarC_Ident.path_of_lid
                                               ed.FStarC_Syntax_Syntax.mname in
                                           let p' =
                                             apply_last
                                               (fun s ->
                                                  Prims.strcat "__"
                                                    (Prims.strcat s
                                                       (Prims.strcat
                                                          "_eff_override_"
                                                          name))) p in
                                           let l' =
                                             FStarC_Ident.lid_of_path p'
                                               ed_range in
                                           let uu___14 =
                                             FStarC_TypeChecker_Env.try_lookup_lid
                                               env2 l' in
                                           match uu___14 with
                                           | FStar_Pervasives_Native.Some
                                               (_us, _t) ->
                                               ((let uu___16 =
                                                   FStarC_Compiler_Debug.any
                                                     () in
                                                 if uu___16
                                                 then
                                                   let uu___17 =
                                                     FStarC_Ident.string_of_lid
                                                       l' in
                                                   FStarC_Compiler_Util.print1
                                                     "DM4F: Applying override %s\n"
                                                     uu___17
                                                 else ());
                                                (let uu___16 =
                                                   FStarC_Syntax_Syntax.lid_and_dd_as_fv
                                                     l'
                                                     FStar_Pervasives_Native.None in
                                                 FStarC_Syntax_Syntax.fv_to_tm
                                                   uu___16))
                                           | FStar_Pervasives_Native.None ->
                                               let uu___15 =
                                                 let uu___16 = mk_lid name in
                                                 let uu___17 =
                                                   FStarC_Syntax_Util.abs
                                                     effect_binders1 item
                                                     FStar_Pervasives_Native.None in
                                                 mk_toplevel_definition env2
                                                   uu___16 uu___17 in
                                               (match uu___15 with
                                                | (sigelt, fv) ->
                                                    let sigelt1 =
                                                      if maybe_admit1
                                                      then
                                                        {
                                                          FStarC_Syntax_Syntax.sigel
                                                            =
                                                            (sigelt.FStarC_Syntax_Syntax.sigel);
                                                          FStarC_Syntax_Syntax.sigrng
                                                            =
                                                            (sigelt.FStarC_Syntax_Syntax.sigrng);
                                                          FStarC_Syntax_Syntax.sigquals
                                                            =
                                                            (sigelt.FStarC_Syntax_Syntax.sigquals);
                                                          FStarC_Syntax_Syntax.sigmeta
                                                            =
                                                            (let uu___16 =
                                                               sigelt.FStarC_Syntax_Syntax.sigmeta in
                                                             {
                                                               FStarC_Syntax_Syntax.sigmeta_active
                                                                 =
                                                                 (uu___16.FStarC_Syntax_Syntax.sigmeta_active);
                                                               FStarC_Syntax_Syntax.sigmeta_fact_db_ids
                                                                 =
                                                                 (uu___16.FStarC_Syntax_Syntax.sigmeta_fact_db_ids);
                                                               FStarC_Syntax_Syntax.sigmeta_admit
                                                                 = true;
                                                               FStarC_Syntax_Syntax.sigmeta_spliced
                                                                 =
                                                                 (uu___16.FStarC_Syntax_Syntax.sigmeta_spliced);
                                                               FStarC_Syntax_Syntax.sigmeta_already_checked
                                                                 =
                                                                 (uu___16.FStarC_Syntax_Syntax.sigmeta_already_checked);
                                                               FStarC_Syntax_Syntax.sigmeta_extension_data
                                                                 =
                                                                 (uu___16.FStarC_Syntax_Syntax.sigmeta_extension_data)
                                                             });
                                                          FStarC_Syntax_Syntax.sigattrs
                                                            =
                                                            (sigelt.FStarC_Syntax_Syntax.sigattrs);
                                                          FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                                            =
                                                            (sigelt.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                                          FStarC_Syntax_Syntax.sigopts
                                                            =
                                                            (sigelt.FStarC_Syntax_Syntax.sigopts)
                                                        }
                                                      else sigelt in
                                                    ((let uu___17 =
                                                        let uu___18 =
                                                          FStarC_Compiler_Effect.op_Bang
                                                            sigelts in
                                                        sigelt1 :: uu___18 in
                                                      FStarC_Compiler_Effect.op_Colon_Equals
                                                        sigelts uu___17);
                                                     fv)) in
                                         let register_admit = register true in
                                         let register1 = register false in
                                         let lift_from_pure_wp1 =
                                           register1 "lift_from_pure"
                                             lift_from_pure_wp in
                                         let mk_sigelt se =
                                           let uu___14 =
                                             FStarC_Syntax_Syntax.mk_sigelt
                                               se in
                                           {
                                             FStarC_Syntax_Syntax.sigel =
                                               (uu___14.FStarC_Syntax_Syntax.sigel);
                                             FStarC_Syntax_Syntax.sigrng =
                                               ed_range;
                                             FStarC_Syntax_Syntax.sigquals =
                                               (uu___14.FStarC_Syntax_Syntax.sigquals);
                                             FStarC_Syntax_Syntax.sigmeta =
                                               (uu___14.FStarC_Syntax_Syntax.sigmeta);
                                             FStarC_Syntax_Syntax.sigattrs =
                                               (uu___14.FStarC_Syntax_Syntax.sigattrs);
                                             FStarC_Syntax_Syntax.sigopens_and_abbrevs
                                               =
                                               (uu___14.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                                             FStarC_Syntax_Syntax.sigopts =
                                               (uu___14.FStarC_Syntax_Syntax.sigopts)
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
                                           FStarC_Compiler_List.fold_left
                                             (fun uu___15 ->
                                                fun action ->
                                                  match uu___15 with
                                                  | (dmff_env3, actions) ->
                                                      let params_un =
                                                        FStarC_Syntax_Subst.open_binders
                                                          action.FStarC_Syntax_Syntax.action_params in
                                                      let uu___16 =
                                                        let uu___17 =
                                                          get_env dmff_env3 in
                                                        FStarC_TypeChecker_TcTerm.tc_tparams
                                                          uu___17 params_un in
                                                      (match uu___16 with
                                                       | (action_params,
                                                          env', uu___17) ->
                                                           let action_params1
                                                             =
                                                             FStarC_Compiler_List.map
                                                               (fun b ->
                                                                  let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    b.FStarC_Syntax_Syntax.binder_bv in
                                                                    let uu___20
                                                                    =
                                                                    FStarC_TypeChecker_Normalize.normalize
                                                                    [FStarC_TypeChecker_Env.EraseUniverses]
                                                                    env'
                                                                    (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    {
                                                                    FStarC_Syntax_Syntax.ppname
                                                                    =
                                                                    (uu___19.FStarC_Syntax_Syntax.ppname);
                                                                    FStarC_Syntax_Syntax.index
                                                                    =
                                                                    (uu___19.FStarC_Syntax_Syntax.index);
                                                                    FStarC_Syntax_Syntax.sort
                                                                    = uu___20
                                                                    } in
                                                                  {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = uu___18;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_qual);
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_positivity);
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (b.FStarC_Syntax_Syntax.binder_attrs)
                                                                  })
                                                               action_params in
                                                           let dmff_env' =
                                                             set_env
                                                               dmff_env3 env' in
                                                           let uu___18 =
                                                             elaborate_and_star
                                                               dmff_env'
                                                               action_params1
                                                               ((action.FStarC_Syntax_Syntax.action_univs),
                                                                 (action.FStarC_Syntax_Syntax.action_defn)) in
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
                                                                    FStarC_Ident.ident_of_lid
                                                                    action.FStarC_Syntax_Syntax.action_name in
                                                                  FStarC_Ident.string_of_id
                                                                    uu___19 in
                                                                let action_typ_with_wp
                                                                  =
                                                                  trans_F
                                                                    dmff_env'
                                                                    action_t
                                                                    action_wp in
                                                                let action_params2
                                                                  =
                                                                  FStarC_Syntax_Subst.close_binders
                                                                    action_params1 in
                                                                let action_elab1
                                                                  =
                                                                  FStarC_Syntax_Subst.close
                                                                    action_params2
                                                                    action_elab in
                                                                let action_typ_with_wp1
                                                                  =
                                                                  FStarC_Syntax_Subst.close
                                                                    action_params2
                                                                    action_typ_with_wp in
                                                                let action_elab2
                                                                  =
                                                                  FStarC_Syntax_Util.abs
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
                                                                    FStarC_Syntax_Syntax.mk_Total
                                                                    action_typ_with_wp1 in
                                                                    FStarC_Syntax_Util.flat_arrow
                                                                    action_params2
                                                                    uu___20 in
                                                                ((let uu___20
                                                                    =
                                                                    FStarC_Compiler_Effect.op_Bang
                                                                    dbg in
                                                                  if uu___20
                                                                  then
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    (FStarC_Class_Show.show_list
                                                                    FStarC_Syntax_Print.showable_binder)
                                                                    params_un in
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    (FStarC_Class_Show.show_list
                                                                    FStarC_Syntax_Print.showable_binder)
                                                                    action_params2 in
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    action_typ_with_wp2 in
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    action_elab2 in
                                                                    FStarC_Compiler_Util.print4
                                                                    "original action_params %s, end action_params %s, type %s, term %s\n"
                                                                    uu___21
                                                                    uu___22
                                                                    uu___23
                                                                    uu___24
                                                                  else ());
                                                                 (let action_elab3
                                                                    =
                                                                    register1
                                                                    (Prims.strcat
                                                                    name
                                                                    "_elab")
                                                                    action_elab2 in
                                                                  let action_typ_with_wp3
                                                                    =
                                                                    register1
                                                                    (Prims.strcat
                                                                    name
                                                                    "_complete_type")
                                                                    action_typ_with_wp2 in
                                                                  let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    apply_close
                                                                    action_elab3 in
                                                                    let uu___23
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp3 in
                                                                    {
                                                                    FStarC_Syntax_Syntax.action_name
                                                                    =
                                                                    (action.FStarC_Syntax_Syntax.action_name);
                                                                    FStarC_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (action.FStarC_Syntax_Syntax.action_unqualified_name);
                                                                    FStarC_Syntax_Syntax.action_univs
                                                                    =
                                                                    (action.FStarC_Syntax_Syntax.action_univs);
                                                                    FStarC_Syntax_Syntax.action_params
                                                                    = [];
                                                                    FStarC_Syntax_Syntax.action_defn
                                                                    = uu___22;
                                                                    FStarC_Syntax_Syntax.action_typ
                                                                    = uu___23
                                                                    } in
                                                                    uu___21
                                                                    ::
                                                                    actions in
                                                                  (dmff_env4,
                                                                    uu___20))))))
                                             (dmff_env2, [])
                                             ed.FStarC_Syntax_Syntax.actions in
                                         (match uu___14 with
                                          | (dmff_env3, actions) ->
                                              let actions1 =
                                                FStarC_Compiler_List.rev
                                                  actions in
                                              let repr1 =
                                                let wp =
                                                  FStarC_Syntax_Syntax.gen_bv
                                                    "wp_a"
                                                    FStar_Pervasives_Native.None
                                                    wp_a in
                                                let binders =
                                                  let uu___15 =
                                                    FStarC_Syntax_Syntax.mk_binder
                                                      a1 in
                                                  let uu___16 =
                                                    let uu___17 =
                                                      FStarC_Syntax_Syntax.mk_binder
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
                                                              FStarC_Syntax_Syntax.bv_to_name
                                                                a1 in
                                                            let uu___22 =
                                                              FStarC_Syntax_Syntax.as_aqual_implicit
                                                                false in
                                                            (uu___21,
                                                              uu___22) in
                                                          [uu___20] in
                                                        {
                                                          FStarC_Syntax_Syntax.hd
                                                            = repr;
                                                          FStarC_Syntax_Syntax.args
                                                            = uu___19
                                                        } in
                                                      FStarC_Syntax_Syntax.Tm_app
                                                        uu___18 in
                                                    mk uu___17 in
                                                  let uu___17 =
                                                    FStarC_Syntax_Syntax.bv_to_name
                                                      wp in
                                                  trans_F dmff_env3 uu___16
                                                    uu___17 in
                                                FStarC_Syntax_Util.abs
                                                  binders uu___15
                                                  FStar_Pervasives_Native.None in
                                              let uu___15 =
                                                recheck_debug "FC" env2 repr1 in
                                              let repr2 =
                                                register1 "repr" repr1 in
                                              let uu___16 =
                                                let uu___17 =
                                                  let uu___18 =
                                                    let uu___19 =
                                                      FStarC_Syntax_Subst.compress
                                                        wp_type in
                                                    FStarC_Syntax_Util.unascribe
                                                      uu___19 in
                                                  uu___18.FStarC_Syntax_Syntax.n in
                                                match uu___17 with
                                                | FStarC_Syntax_Syntax.Tm_abs
                                                    {
                                                      FStarC_Syntax_Syntax.bs
                                                        =
                                                        type_param::effect_param;
                                                      FStarC_Syntax_Syntax.body
                                                        = arrow;
                                                      FStarC_Syntax_Syntax.rc_opt
                                                        = uu___18;_}
                                                    ->
                                                    let uu___19 =
                                                      let uu___20 =
                                                        FStarC_Syntax_Subst.open_term
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
                                                               FStarC_Syntax_Subst.compress
                                                                 arrow1 in
                                                             FStarC_Syntax_Util.unascribe
                                                               uu___22 in
                                                           uu___21.FStarC_Syntax_Syntax.n in
                                                         (match uu___20 with
                                                          | FStarC_Syntax_Syntax.Tm_arrow
                                                              {
                                                                FStarC_Syntax_Syntax.bs1
                                                                  =
                                                                  wp_binders;
                                                                FStarC_Syntax_Syntax.comp
                                                                  = c;_}
                                                              ->
                                                              let uu___21 =
                                                                FStarC_Syntax_Subst.open_comp
                                                                  wp_binders
                                                                  c in
                                                              (match uu___21
                                                               with
                                                               | (wp_binders1,
                                                                  c1) ->
                                                                   let uu___22
                                                                    =
                                                                    FStarC_Compiler_List.partition
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStarC_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStarC_Syntax_Syntax.binder_qual
                                                                    = uu___24;
                                                                    FStarC_Syntax_Syntax.binder_positivity
                                                                    = uu___25;
                                                                    FStarC_Syntax_Syntax.binder_attrs
                                                                    = uu___26;_}
                                                                    ->
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Syntax_Free.names
                                                                    bv.FStarC_Syntax_Syntax.sort in
                                                                    FStarC_Class_Setlike.mem
                                                                    ()
                                                                    (Obj.magic
                                                                    (FStarC_Compiler_FlatSet.setlike_flat_set
                                                                    FStarC_Syntax_Syntax.ord_bv))
                                                                    type_param1.FStarC_Syntax_Syntax.binder_bv
                                                                    (Obj.magic
                                                                    uu___28) in
                                                                    Prims.op_Negation
                                                                    uu___27)
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
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    arrow1 in
                                                                    FStarC_Compiler_Util.format1
                                                                    "Impossible to generate DM effect: no post candidate %s (Type variable does not appear)"
                                                                    uu___23 in
                                                                    FStarC_Errors.raise_error0
                                                                    FStarC_Errors_Codes.Fatal_ImpossibleToGenerateDMEffect
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    err_msg)
                                                                    | 
                                                                    uu___23
                                                                    ->
                                                                    let err_msg
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    arrow1 in
                                                                    FStarC_Compiler_Util.format1
                                                                    "Impossible to generate DM effect: multiple post candidates %s"
                                                                    uu___24 in
                                                                    FStarC_Errors.raise_error0
                                                                    FStarC_Errors_Codes.Fatal_ImpossibleToGenerateDMEffect
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_string)
                                                                    (Obj.magic
                                                                    err_msg) in
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1 in
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (post.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort
                                                                    FStar_Pervasives_Native.None in
                                                                    (uu___23,
                                                                    uu___24)))
                                                          | uu___21 ->
                                                              let uu___22 =
                                                                let uu___23 =
                                                                  FStarC_Class_Show.show
                                                                    FStarC_Syntax_Print.showable_term
                                                                    arrow1 in
                                                                FStarC_Compiler_Util.format1
                                                                  "Impossible: pre/post arrow %s"
                                                                  uu___23 in
                                                              raise_error
                                                                FStarC_Errors_Codes.Fatal_ImpossiblePrePostArrow
                                                                uu___22))
                                                | uu___18 ->
                                                    let uu___19 =
                                                      let uu___20 =
                                                        FStarC_Class_Show.show
                                                          FStarC_Syntax_Print.showable_term
                                                          wp_type in
                                                      FStarC_Compiler_Util.format1
                                                        "Impossible: pre/post abs %s"
                                                        uu___20 in
                                                    raise_error
                                                      FStarC_Errors_Codes.Fatal_ImpossiblePrePostAbs
                                                      uu___19 in
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
                                                       match ed.FStarC_Syntax_Syntax.combinators
                                                       with
                                                       | FStarC_Syntax_Syntax.DM4F_eff
                                                           combs ->
                                                           let uu___20 =
                                                             let uu___21 =
                                                               let uu___22 =
                                                                 apply_close
                                                                   return_wp2 in
                                                               ([], uu___22) in
                                                             let uu___22 =
                                                               let uu___23 =
                                                                 apply_close
                                                                   bind_wp2 in
                                                               ([], uu___23) in
                                                             let uu___23 =
                                                               let uu___24 =
                                                                 let uu___25
                                                                   =
                                                                   apply_close
                                                                    repr2 in
                                                                 ([],
                                                                   uu___25) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___24 in
                                                             let uu___24 =
                                                               let uu___25 =
                                                                 let uu___26
                                                                   =
                                                                   apply_close
                                                                    return_elab1 in
                                                                 ([],
                                                                   uu___26) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___25 in
                                                             let uu___25 =
                                                               let uu___26 =
                                                                 let uu___27
                                                                   =
                                                                   apply_close
                                                                    bind_elab1 in
                                                                 ([],
                                                                   uu___27) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___26 in
                                                             {
                                                               FStarC_Syntax_Syntax.ret_wp
                                                                 = uu___21;
                                                               FStarC_Syntax_Syntax.bind_wp
                                                                 = uu___22;
                                                               FStarC_Syntax_Syntax.stronger
                                                                 =
                                                                 (combs.FStarC_Syntax_Syntax.stronger);
                                                               FStarC_Syntax_Syntax.if_then_else
                                                                 =
                                                                 (combs.FStarC_Syntax_Syntax.if_then_else);
                                                               FStarC_Syntax_Syntax.ite_wp
                                                                 =
                                                                 (combs.FStarC_Syntax_Syntax.ite_wp);
                                                               FStarC_Syntax_Syntax.close_wp
                                                                 =
                                                                 (combs.FStarC_Syntax_Syntax.close_wp);
                                                               FStarC_Syntax_Syntax.trivial
                                                                 =
                                                                 (combs.FStarC_Syntax_Syntax.trivial);
                                                               FStarC_Syntax_Syntax.repr
                                                                 = uu___23;
                                                               FStarC_Syntax_Syntax.return_repr
                                                                 = uu___24;
                                                               FStarC_Syntax_Syntax.bind_repr
                                                                 = uu___25
                                                             } in
                                                           FStarC_Syntax_Syntax.DM4F_eff
                                                             uu___20
                                                       | uu___20 ->
                                                           failwith
                                                             "Impossible! For a DM4F effect combinators must be in DM4f_eff" in
                                                     let ed1 =
                                                       let uu___20 =
                                                         FStarC_Syntax_Subst.close_binders
                                                           effect_binders1 in
                                                       let uu___21 =
                                                         let uu___22 =
                                                           let uu___23 =
                                                             FStarC_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature in
                                                           ([], uu___23) in
                                                         FStarC_Syntax_Syntax.WP_eff_sig
                                                           uu___22 in
                                                       {
                                                         FStarC_Syntax_Syntax.mname
                                                           =
                                                           (ed.FStarC_Syntax_Syntax.mname);
                                                         FStarC_Syntax_Syntax.cattributes
                                                           =
                                                           (ed.FStarC_Syntax_Syntax.cattributes);
                                                         FStarC_Syntax_Syntax.univs
                                                           =
                                                           (ed.FStarC_Syntax_Syntax.univs);
                                                         FStarC_Syntax_Syntax.binders
                                                           = uu___20;
                                                         FStarC_Syntax_Syntax.signature
                                                           = uu___21;
                                                         FStarC_Syntax_Syntax.combinators
                                                           = ed_combs;
                                                         FStarC_Syntax_Syntax.actions
                                                           = actions1;
                                                         FStarC_Syntax_Syntax.eff_attrs
                                                           =
                                                           (ed.FStarC_Syntax_Syntax.eff_attrs);
                                                         FStarC_Syntax_Syntax.extraction_mode
                                                           =
                                                           (ed.FStarC_Syntax_Syntax.extraction_mode)
                                                       } in
                                                     let uu___20 =
                                                       gen_wps_for_free env2
                                                         effect_binders1 a1
                                                         wp_a ed1 in
                                                     match uu___20 with
                                                     | (sigelts', ed2) ->
                                                         ((let uu___22 =
                                                             FStarC_Compiler_Effect.op_Bang
                                                               dbg in
                                                           if uu___22
                                                           then
                                                             let uu___23 =
                                                               FStarC_Class_Show.show
                                                                 FStarC_Syntax_Print.showable_eff_decl
                                                                 ed2 in
                                                             FStarC_Compiler_Util.print_string
                                                               uu___23
                                                           else ());
                                                          (let lift_from_pure_opt
                                                             =
                                                             if
                                                               (FStarC_Compiler_List.length
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
                                                                   FStarC_Syntax_Syntax.source
                                                                    =
                                                                    FStarC_Parser_Const.effect_PURE_lid;
                                                                   FStarC_Syntax_Syntax.target
                                                                    =
                                                                    (ed2.FStarC_Syntax_Syntax.mname);
                                                                   FStarC_Syntax_Syntax.lift_wp
                                                                    = uu___22;
                                                                   FStarC_Syntax_Syntax.lift
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                   FStarC_Syntax_Syntax.kind
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                 } in
                                                               let uu___22 =
                                                                 mk_sigelt
                                                                   (FStarC_Syntax_Syntax.Sig_sub_effect
                                                                    lift_from_pure) in
                                                               FStar_Pervasives_Native.Some
                                                                 uu___22
                                                             else
                                                               FStar_Pervasives_Native.None in
                                                           let uu___22 =
                                                             let uu___23 =
                                                               let uu___24 =
                                                                 FStarC_Compiler_Effect.op_Bang
                                                                   sigelts in
                                                               FStarC_Compiler_List.rev
                                                                 uu___24 in
                                                             FStarC_Compiler_List.op_At
                                                               uu___23
                                                               sigelts' in
                                                           (uu___22, ed2,
                                                             lift_from_pure_opt))))))))))))))