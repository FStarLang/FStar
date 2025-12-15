open Prims
type uenv = FStarC_Extraction_ML_UEnv.uenv
let dbg_dep : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Dep"
let module_or_interface_name (m : FStarC_Syntax_Syntax.modul) :
  (Prims.bool * FStarC_Ident.lid)=
  ((m.FStarC_Syntax_Syntax.is_interface), (m.FStarC_Syntax_Syntax.name))
let with_dsenv_of_tcenv (tcenv : FStarC_TypeChecker_Env.env)
  (f : 'a FStarC_Syntax_DsEnv.withenv) : ('a * FStarC_TypeChecker_Env.env)=
  let uu___ = f tcenv.FStarC_TypeChecker_Env.dsenv in
  match uu___ with
  | (a1, dsenv) ->
      (a1,
        {
          FStarC_TypeChecker_Env.solver =
            (tcenv.FStarC_TypeChecker_Env.solver);
          FStarC_TypeChecker_Env.range = (tcenv.FStarC_TypeChecker_Env.range);
          FStarC_TypeChecker_Env.curmodule =
            (tcenv.FStarC_TypeChecker_Env.curmodule);
          FStarC_TypeChecker_Env.gamma = (tcenv.FStarC_TypeChecker_Env.gamma);
          FStarC_TypeChecker_Env.gamma_sig =
            (tcenv.FStarC_TypeChecker_Env.gamma_sig);
          FStarC_TypeChecker_Env.gamma_cache =
            (tcenv.FStarC_TypeChecker_Env.gamma_cache);
          FStarC_TypeChecker_Env.modules =
            (tcenv.FStarC_TypeChecker_Env.modules);
          FStarC_TypeChecker_Env.expected_typ =
            (tcenv.FStarC_TypeChecker_Env.expected_typ);
          FStarC_TypeChecker_Env.sigtab =
            (tcenv.FStarC_TypeChecker_Env.sigtab);
          FStarC_TypeChecker_Env.attrtab =
            (tcenv.FStarC_TypeChecker_Env.attrtab);
          FStarC_TypeChecker_Env.instantiate_imp =
            (tcenv.FStarC_TypeChecker_Env.instantiate_imp);
          FStarC_TypeChecker_Env.effects =
            (tcenv.FStarC_TypeChecker_Env.effects);
          FStarC_TypeChecker_Env.generalize =
            (tcenv.FStarC_TypeChecker_Env.generalize);
          FStarC_TypeChecker_Env.letrecs =
            (tcenv.FStarC_TypeChecker_Env.letrecs);
          FStarC_TypeChecker_Env.top_level =
            (tcenv.FStarC_TypeChecker_Env.top_level);
          FStarC_TypeChecker_Env.check_uvars =
            (tcenv.FStarC_TypeChecker_Env.check_uvars);
          FStarC_TypeChecker_Env.use_eq_strict =
            (tcenv.FStarC_TypeChecker_Env.use_eq_strict);
          FStarC_TypeChecker_Env.is_iface =
            (tcenv.FStarC_TypeChecker_Env.is_iface);
          FStarC_TypeChecker_Env.admit = (tcenv.FStarC_TypeChecker_Env.admit);
          FStarC_TypeChecker_Env.phase1 =
            (tcenv.FStarC_TypeChecker_Env.phase1);
          FStarC_TypeChecker_Env.failhard =
            (tcenv.FStarC_TypeChecker_Env.failhard);
          FStarC_TypeChecker_Env.flychecking =
            (tcenv.FStarC_TypeChecker_Env.flychecking);
          FStarC_TypeChecker_Env.uvar_subtyping =
            (tcenv.FStarC_TypeChecker_Env.uvar_subtyping);
          FStarC_TypeChecker_Env.intactics =
            (tcenv.FStarC_TypeChecker_Env.intactics);
          FStarC_TypeChecker_Env.nocoerce =
            (tcenv.FStarC_TypeChecker_Env.nocoerce);
          FStarC_TypeChecker_Env.tc_term =
            (tcenv.FStarC_TypeChecker_Env.tc_term);
          FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
            (tcenv.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
          FStarC_TypeChecker_Env.universe_of =
            (tcenv.FStarC_TypeChecker_Env.universe_of);
          FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
            (tcenv.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
          FStarC_TypeChecker_Env.teq_nosmt_force =
            (tcenv.FStarC_TypeChecker_Env.teq_nosmt_force);
          FStarC_TypeChecker_Env.subtype_nosmt_force =
            (tcenv.FStarC_TypeChecker_Env.subtype_nosmt_force);
          FStarC_TypeChecker_Env.qtbl_name_and_index =
            (tcenv.FStarC_TypeChecker_Env.qtbl_name_and_index);
          FStarC_TypeChecker_Env.normalized_eff_names =
            (tcenv.FStarC_TypeChecker_Env.normalized_eff_names);
          FStarC_TypeChecker_Env.fv_delta_depths =
            (tcenv.FStarC_TypeChecker_Env.fv_delta_depths);
          FStarC_TypeChecker_Env.proof_ns =
            (tcenv.FStarC_TypeChecker_Env.proof_ns);
          FStarC_TypeChecker_Env.synth_hook =
            (tcenv.FStarC_TypeChecker_Env.synth_hook);
          FStarC_TypeChecker_Env.try_solve_implicits_hook =
            (tcenv.FStarC_TypeChecker_Env.try_solve_implicits_hook);
          FStarC_TypeChecker_Env.splice =
            (tcenv.FStarC_TypeChecker_Env.splice);
          FStarC_TypeChecker_Env.mpreprocess =
            (tcenv.FStarC_TypeChecker_Env.mpreprocess);
          FStarC_TypeChecker_Env.postprocess =
            (tcenv.FStarC_TypeChecker_Env.postprocess);
          FStarC_TypeChecker_Env.identifier_info =
            (tcenv.FStarC_TypeChecker_Env.identifier_info);
          FStarC_TypeChecker_Env.tc_hooks =
            (tcenv.FStarC_TypeChecker_Env.tc_hooks);
          FStarC_TypeChecker_Env.dsenv = dsenv;
          FStarC_TypeChecker_Env.nbe = (tcenv.FStarC_TypeChecker_Env.nbe);
          FStarC_TypeChecker_Env.strict_args_tab =
            (tcenv.FStarC_TypeChecker_Env.strict_args_tab);
          FStarC_TypeChecker_Env.erasable_types_tab =
            (tcenv.FStarC_TypeChecker_Env.erasable_types_tab);
          FStarC_TypeChecker_Env.enable_defer_to_tac =
            (tcenv.FStarC_TypeChecker_Env.enable_defer_to_tac);
          FStarC_TypeChecker_Env.unif_allow_ref_guards =
            (tcenv.FStarC_TypeChecker_Env.unif_allow_ref_guards);
          FStarC_TypeChecker_Env.erase_erasable_args =
            (tcenv.FStarC_TypeChecker_Env.erase_erasable_args);
          FStarC_TypeChecker_Env.core_check =
            (tcenv.FStarC_TypeChecker_Env.core_check);
          FStarC_TypeChecker_Env.missing_decl =
            (tcenv.FStarC_TypeChecker_Env.missing_decl)
        })
let with_tcenv_of_env (e : uenv)
  (f : FStarC_TypeChecker_Env.env -> ('a * FStarC_TypeChecker_Env.env)) :
  ('a * uenv)=
  let uu___ =
    let uu___1 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv e in f uu___1 in
  match uu___ with
  | (a1, t') ->
      let uu___1 = FStarC_Extraction_ML_UEnv.set_tcenv e t' in (a1, uu___1)
let with_dsenv_of_env (e : uenv) (f : 'a FStarC_Syntax_DsEnv.withenv) :
  ('a * uenv)=
  let uu___ =
    let uu___1 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv e in
    with_dsenv_of_tcenv uu___1 f in
  match uu___ with
  | (a1, tcenv) ->
      let uu___1 = FStarC_Extraction_ML_UEnv.set_tcenv e tcenv in
      (a1, uu___1)
let push_env (env : uenv) : uenv=
  let uu___ =
    with_tcenv_of_env env
      (fun tcenv ->
         let uu___1 =
           let uu___2 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env in
           FStarC_TypeChecker_Env.push uu___2 "top-level: push_env" in
         ((), uu___1)) in
  FStar_Pervasives_Native.snd uu___
let pop_env (env : uenv) : uenv=
  let uu___ =
    with_tcenv_of_env env
      (fun tcenv ->
         let uu___1 = FStarC_TypeChecker_Env.pop tcenv "top-level: pop_env" in
         ((), uu___1)) in
  FStar_Pervasives_Native.snd uu___
let with_env (env : uenv) (f : uenv -> 'a) : 'a=
  let env1 = push_env env in
  let res = f env1 in let uu___ = pop_env env1 in res
let env_of_tcenv (env : FStarC_TypeChecker_Env.env) :
  FStarC_Extraction_ML_UEnv.uenv= FStarC_Extraction_ML_UEnv.new_uenv env
let parse (fly_deps : Prims.bool) (env : uenv)
  (interface_fn : Prims.string FStar_Pervasives_Native.option)
  (fn : Prims.string) :
  (FStarC_Ident.lident * (FStarC_Parser_AST.modul,
    FStarC_Syntax_Syntax.modul) FStar_Pervasives.either * uenv)=
  let uu___ = FStarC_Parser_Driver.parse_file fn in
  match uu___ with
  | (ast, uu___1) ->
      let uu___2 =
        match interface_fn with
        | FStar_Pervasives_Native.None -> (ast, env)
        | FStar_Pervasives_Native.Some interface_fn1 ->
            let uu___3 = FStarC_Parser_Driver.parse_file interface_fn1 in
            (match uu___3 with
             | (pre_ast, uu___4) ->
                 (match (pre_ast, ast) with
                  | (FStarC_Parser_AST.Interface
                     { FStarC_Parser_AST.no_prelude1 = uu___5;
                       FStarC_Parser_AST.mname1 = lid1;
                       FStarC_Parser_AST.decls1 = decls1;
                       FStarC_Parser_AST.admitted = uu___6;_},
                     FStarC_Parser_AST.Module
                     { FStarC_Parser_AST.no_prelude = uu___7;
                       FStarC_Parser_AST.mname = lid2;
                       FStarC_Parser_AST.decls = decls2;_})
                      when FStarC_Ident.lid_equals lid1 lid2 ->
                      let uu___8 =
                        let uu___9 =
                          FStarC_ToSyntax_Interleave.initialize_interface
                            lid1 decls1 in
                        with_dsenv_of_env env uu___9 in
                      (match uu___8 with
                       | (uu___9, env1) ->
                           let uu___10 =
                             FStarC_ToSyntax_Interleave.interleave_module ast
                               true in
                           with_dsenv_of_env env1 uu___10)
                  | (FStarC_Parser_AST.Interface
                     { FStarC_Parser_AST.no_prelude1 = uu___5;
                       FStarC_Parser_AST.mname1 = lid1;
                       FStarC_Parser_AST.decls1 = uu___6;
                       FStarC_Parser_AST.admitted = uu___7;_},
                     FStarC_Parser_AST.Interface
                     { FStarC_Parser_AST.no_prelude1 = uu___8;
                       FStarC_Parser_AST.mname1 = lid2;
                       FStarC_Parser_AST.decls1 = uu___9;
                       FStarC_Parser_AST.admitted = uu___10;_})
                      ->
                      FStarC_Errors.raise_error FStarC_Ident.hasrange_lident
                        lid1 FStarC_Errors_Codes.Fatal_PreModuleMismatch ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic
                           "Module name in implementation does not match that of interface.")
                  | uu___5 ->
                      FStarC_Errors.raise_error0
                        FStarC_Errors_Codes.Fatal_PreModuleMismatch ()
                        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                        (Obj.magic
                           "Module name in implementation does not match that of interface."))) in
      (match uu___2 with
       | (ast1, env1) ->
           if fly_deps
           then
             let uu___3 = FStarC_Parser_AST.lid_of_modul ast1 in
             (uu___3, (FStar_Pervasives.Inl ast1), env1)
           else
             (let uu___4 =
                let uu___5 = FStarC_ToSyntax_ToSyntax.ast_modul_to_modul ast1 in
                with_dsenv_of_env env1 uu___5 in
              match uu___4 with
              | (mod1, env2) ->
                  let uu___5 = FStarC_Parser_AST.lid_of_modul ast1 in
                  (uu___5, (FStar_Pervasives.Inr mod1), env2)))
let core_check : FStarC_TypeChecker_Env.core_check_t=
  fun env tm t must_tot ->
    let uu___ =
      let uu___1 = FStarC_Options.compat_pre_core_should_check () in
      Prims.op_Negation uu___1 in
    if uu___
    then FStar_Pervasives.Inl FStar_Pervasives_Native.None
    else
      (let uu___2 = FStarC_TypeChecker_Core.check_term env tm t must_tot in
       match uu___2 with
       | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
           FStar_Pervasives.Inl FStar_Pervasives_Native.None
       | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
           let uu___3 = FStarC_Options.compat_pre_core_set () in
           if uu___3
           then FStar_Pervasives.Inl FStar_Pervasives_Native.None
           else FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
       | FStar_Pervasives.Inr err ->
           FStar_Pervasives.Inr
             ((fun b ->
                 if b
                 then FStarC_TypeChecker_Core.print_error_short err
                 else FStarC_TypeChecker_Core.print_error err)))
type lang_decls_t = FStarC_Parser_AST.decl Prims.list
let parse_frag (frag : FStarC_Parser_ParseIt.input_frag)
  (lang_decls : lang_decls_t) : FStarC_Parser_Driver.fragment=
  let use_lang_decl ds =
    FStarC_List.tryFind
      (fun d -> FStarC_Parser_AST.uu___is_UseLangDecls d.FStarC_Parser_AST.d)
      ds in
  let uu___ = use_lang_decl lang_decls in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      FStarC_Parser_Driver.parse_fragment FStar_Pervasives_Native.None frag
  | FStar_Pervasives_Native.Some
      { FStarC_Parser_AST.d = FStarC_Parser_AST.UseLangDecls lang;
        FStarC_Parser_AST.drange = uu___1; FStarC_Parser_AST.quals = uu___2;
        FStarC_Parser_AST.attrs = uu___3;
        FStarC_Parser_AST.interleaved = uu___4;_}
      ->
      FStarC_Parser_Driver.parse_fragment (FStar_Pervasives_Native.Some lang)
        frag
let tc_one_fragment (is_interface : Prims.bool)
  (curmod : FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  (env : FStarC_TypeChecker_Env.env_t)
  (frag :
    ((FStarC_Parser_ParseIt.input_frag * lang_decls_t),
      FStarC_Parser_AST.decl) FStar_Pervasives.either)
  :
  (FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option *
    FStarC_TypeChecker_Env.env * lang_decls_t)=
  let fname env1 =
    let uu___ = FStarC_Options.file_list () in FStarC_List.hd uu___ in
  let acceptable_mod_name ast_modul =
    let uu___ =
      let uu___1 = fname env in
      FStarC_Parser_Dep.lowercase_module_name uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Parser_AST.lid_of_modul ast_modul in
        FStarC_Ident.string_of_lid uu___3 in
      FStarC_String.lowercase uu___2 in
    uu___ = uu___1 in
  let range_of_first_mod_decl modul =
    match modul with
    | FStarC_Parser_AST.Module
        { FStarC_Parser_AST.no_prelude = uu___;
          FStarC_Parser_AST.mname = uu___1;
          FStarC_Parser_AST.decls = d::uu___2;_}
        -> d.FStarC_Parser_AST.drange
    | FStarC_Parser_AST.Interface
        { FStarC_Parser_AST.no_prelude1 = uu___;
          FStarC_Parser_AST.mname1 = uu___1;
          FStarC_Parser_AST.decls1 = d::uu___2;
          FStarC_Parser_AST.admitted = uu___3;_}
        -> d.FStarC_Parser_AST.drange
    | uu___ -> FStarC_Range_Type.dummyRange in
  let filter_lang_decls d =
    match d.FStarC_Parser_AST.d with
    | FStarC_Parser_AST.UseLangDecls uu___ -> true
    | uu___ -> false in
  let check_module_name_declaration ast_modul =
    let uu___ =
      let uu___1 =
        (FStarC_Options.interactive ()) &&
          (let uu___2 = FStarC_Parser_Dep.fly_deps_enabled () in
           Prims.op_Negation uu___2) in
      if uu___1
      then
        let uu___2 =
          FStarC_ToSyntax_Interleave.interleave_module ast_modul false in
        with_dsenv_of_tcenv env uu___2
      else (ast_modul, env) in
    match uu___ with
    | (ast_modul1, env1) ->
        ((let uu___2 =
            let uu___3 = acceptable_mod_name ast_modul1 in
            Prims.op_Negation uu___3 in
          if uu___2
          then
            let msg =
              let uu___3 =
                let uu___4 = fname env1 in
                FStarC_Parser_Dep.module_name_of_file uu___4 in
              FStarC_Format.fmt1
                "Interactive mode only supports a single module at the top-level. Expected module %s"
                uu___3 in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
              (range_of_first_mod_decl ast_modul1)
              FStarC_Errors_Codes.Fatal_NonSingletonTopLevelModule ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic msg)
          else ());
         (let uu___2 =
            let uu___3 =
              FStarC_Syntax_DsEnv.syntax_only
                env1.FStarC_TypeChecker_Env.dsenv in
            if uu___3
            then
              let uu___4 =
                FStarC_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod
                  ast_modul1 in
              with_dsenv_of_tcenv env1 uu___4
            else
              (let uu___5 =
                 let uu___6 =
                   FStarC_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod
                     ast_modul1 in
                 with_dsenv_of_tcenv env1 uu___6 in
               match uu___5 with
               | (m, env2) -> FStarC_TypeChecker_Tc.tc_partial_modul env2 m) in
          match uu___2 with
          | (modul, env2) ->
              let lang_decls =
                let decls =
                  match ast_modul1 with
                  | FStarC_Parser_AST.Module
                      { FStarC_Parser_AST.no_prelude = uu___3;
                        FStarC_Parser_AST.mname = uu___4;
                        FStarC_Parser_AST.decls = decls1;_}
                      -> decls1
                  | FStarC_Parser_AST.Interface
                      { FStarC_Parser_AST.no_prelude1 = uu___3;
                        FStarC_Parser_AST.mname1 = uu___4;
                        FStarC_Parser_AST.decls1 = decls1;
                        FStarC_Parser_AST.admitted = uu___5;_}
                      -> decls1 in
                FStarC_List.filter filter_lang_decls decls in
              ((FStar_Pervasives_Native.Some modul), env2, lang_decls))) in
  let check_decls ast_decls =
    match curmod with
    | FStar_Pervasives_Native.None ->
        let uu___ = FStarC_List.hd ast_decls in
        (match uu___ with
         | { FStarC_Parser_AST.d = uu___1; FStarC_Parser_AST.drange = rng;
             FStarC_Parser_AST.quals = uu___2;
             FStarC_Parser_AST.attrs = uu___3;
             FStarC_Parser_AST.interleaved = uu___4;_} ->
             FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
               rng FStarC_Errors_Codes.Fatal_ModuleFirstStatement ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic "First statement must be a module declaration"))
    | FStar_Pervasives_Native.Some modul ->
        let uu___ =
          let uu___1 =
            (FStarC_Options.interactive ()) &&
              (let uu___2 = FStarC_Parser_Dep.fly_deps_enabled () in
               Prims.op_Negation uu___2) in
          if uu___1
          then
            FStarC_Util.fold_map
              (fun env1 a_decl ->
                 let uu___2 =
                   let uu___3 =
                     FStarC_ToSyntax_Interleave.prefix_with_interface_decls
                       a_decl in
                   with_dsenv_of_tcenv env1 uu___3 in
                 match uu___2 with | (decls, env2) -> (env2, decls)) env
              ast_decls
          else (env, [ast_decls]) in
        (match uu___ with
         | (env1, ast_decls_l) ->
             let ast_decls1 = FStarC_List.flatten ast_decls_l in
             let uu___1 =
               let uu___2 =
                 FStarC_Syntax_DsEnv.syntax_only
                   env1.FStarC_TypeChecker_Env.dsenv in
               if uu___2
               then
                 let uu___3 =
                   let uu___4 =
                     FStarC_ToSyntax_ToSyntax.decls_to_sigelts ast_decls1 in
                   with_dsenv_of_tcenv env1 uu___4 in
                 match uu___3 with | (uu___4, env2) -> (modul, [], env2)
               else
                 (let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        FStarC_Class_Show.show FStarC_Ident.showable_lident
                          modul.FStarC_Syntax_Syntax.name in
                      Prims.strcat "While desugaring module " uu___6 in
                    FStarC_Errors.with_ctx uu___5
                      (fun uu___6 ->
                         let uu___7 =
                           FStarC_ToSyntax_ToSyntax.decls_to_sigelts
                             ast_decls1 in
                         with_dsenv_of_tcenv env1 uu___7) in
                  match uu___4 with
                  | (ses, env2) ->
                      FStarC_TypeChecker_Tc.tc_more_partial_modul env2 modul
                        ses) in
             (match uu___1 with
              | (modul1, uu___2, env2) ->
                  let uu___3 =
                    FStarC_List.filter filter_lang_decls ast_decls1 in
                  ((FStar_Pervasives_Native.Some modul1), env2, uu___3))) in
  match frag with
  | FStar_Pervasives.Inr d ->
      ((let uu___1 = FStarC_Debug.low () in
        if uu___1
        then
          let uu___2 =
            FStarC_Class_Show.show FStarC_Parser_AST.showable_decl d in
          FStarC_Format.print1 "tc_one_fragment: %s\n" uu___2
        else ());
       (match d.FStarC_Parser_AST.d with
        | FStarC_Parser_AST.TopLevelModule lid ->
            let no_prelude =
              (FStarC_Options.no_prelude ()) ||
                (FStarC_List.existsb
                   (fun uu___1 ->
                      match uu___1.FStarC_Parser_AST.tm with
                      | FStarC_Parser_AST.Const (FStarC_Const.Const_string
                          ("no_prelude", uu___2)) -> true
                      | uu___2 -> false) d.FStarC_Parser_AST.attrs) in
            let modul =
              FStarC_Parser_AST.Module
                {
                  FStarC_Parser_AST.no_prelude = no_prelude;
                  FStarC_Parser_AST.mname = lid;
                  FStarC_Parser_AST.decls = [d]
                } in
            let modul1 =
              if is_interface
              then FStarC_Parser_AST.as_interface modul
              else modul in
            check_module_name_declaration modul1
        | uu___1 -> check_decls [d]))
  | FStar_Pervasives.Inl (frag1, lang_decls) ->
      let uu___ = parse_frag frag1 lang_decls in
      (match uu___ with
       | FStarC_Parser_Driver.Empty -> (curmod, env, [])
       | FStarC_Parser_Driver.Decls [] -> (curmod, env, [])
       | FStarC_Parser_Driver.Modul ast_modul ->
           check_module_name_declaration ast_modul
       | FStarC_Parser_Driver.Decls ast_decls -> check_decls ast_decls)
let load_interface_decls (env : FStarC_TypeChecker_Env.env)
  (interface_file_name : Prims.string) : FStarC_TypeChecker_Env.env_t=
  let r =
    FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None
      (FStarC_Parser_ParseIt.Filename interface_file_name) in
  match r with
  | FStarC_Parser_ParseIt.ASTFragment
      (FStar_Pervasives.Inl (FStarC_Parser_AST.Interface
       { FStarC_Parser_AST.no_prelude1 = uu___; FStarC_Parser_AST.mname1 = l;
         FStarC_Parser_AST.decls1 = decls;
         FStarC_Parser_AST.admitted = uu___1;_}),
       uu___2)
      ->
      let uu___3 =
        let uu___4 = FStarC_ToSyntax_Interleave.initialize_interface l decls in
        with_dsenv_of_tcenv env uu___4 in
      FStar_Pervasives_Native.snd uu___3
  | FStarC_Parser_ParseIt.ASTFragment uu___ ->
      let uu___1 =
        FStarC_Format.fmt1
          "Unexpected result from parsing %s; expected a single interface"
          interface_file_name in
      FStarC_Errors.raise_error0 FStarC_Errors_Codes.Fatal_ParseErrors ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___1)
  | FStarC_Parser_ParseIt.ParseError (err, msg, rng) ->
      FStarC_Effect.raise (FStarC_Errors.Error (err, msg, rng, []))
  | FStarC_Parser_ParseIt.Term uu___ ->
      failwith
        "Impossible: parsing a Toplevel always results in an ASTFragment"
let emit (dep_graph : FStarC_Parser_Dep.deps)
  (mllib : (uenv * FStarC_Extraction_ML_Syntax.mlmodule) Prims.list) : 
  unit=
  let opt = FStarC_Options.codegen () in
  let fail uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_option FStarC_Options.showable_codegen_t)
          opt in
      Prims.strcat "Unrecognized extraction backend: " uu___2 in
    failwith uu___1 in
  if opt <> FStar_Pervasives_Native.None
  then
    let ext =
      match opt with
      | FStar_Pervasives_Native.Some (FStarC_Options.FSharp) -> ".fs"
      | FStar_Pervasives_Native.Some (FStarC_Options.OCaml) -> ".ml"
      | FStar_Pervasives_Native.Some (FStarC_Options.Plugin) -> ".ml"
      | FStar_Pervasives_Native.Some (FStarC_Options.PluginNoLib) -> ".ml"
      | FStar_Pervasives_Native.Some (FStarC_Options.Krml) -> ".krml"
      | FStar_Pervasives_Native.Some (FStarC_Options.Extension) -> ".ast"
      | uu___ -> fail () in
    let ofile basename =
      let uu___ = FStarC_Options.output_to () in
      match uu___ with
      | FStar_Pervasives_Native.Some fn -> fn
      | FStar_Pervasives_Native.None ->
          FStarC_Find.prepend_output_dir basename in
    match opt with
    | FStar_Pervasives_Native.Some (FStarC_Options.FSharp) ->
        let printer =
          if opt = (FStar_Pervasives_Native.Some FStarC_Options.FSharp)
          then FStarC_Extraction_ML_PrintFS.print_fs
          else FStarC_Extraction_ML_PrintML.print_ml in
        ((let uu___1 =
            (let uu___2 = FStarC_Options.output_to () in
             FStar_Pervasives_Native.uu___is_Some uu___2) &&
              ((FStarC_List.length mllib) > Prims.int_one) in
          if uu___1
          then
            let uu___2 =
              let uu___3 =
                FStarC_Errors_Msg.text
                  "Cannot provide -o and extract multiple modules" in
              let uu___4 =
                let uu___5 =
                  FStarC_Errors_Msg.text
                    "Please use -o with a single module, or specify an output directory with --odir" in
                [uu___5] in
              uu___3 :: uu___4 in
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___2)
          else ());
         FStarC_List.iter
           (fun uu___1 ->
              match uu___1 with
              | (uu___2, mlmodule) ->
                  let uu___3 = mlmodule in
                  (match uu___3 with
                   | (p, uu___4) ->
                       let filename =
                         let basename =
                           let uu___5 =
                             FStarC_Extraction_ML_Util.flatten_mlpath p in
                           Prims.strcat uu___5 ext in
                         ofile basename in
                       let ml = printer mlmodule in
                       FStarC_Util.write_file filename ml)) mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.OCaml) ->
        let printer =
          if opt = (FStar_Pervasives_Native.Some FStarC_Options.FSharp)
          then FStarC_Extraction_ML_PrintFS.print_fs
          else FStarC_Extraction_ML_PrintML.print_ml in
        ((let uu___1 =
            (let uu___2 = FStarC_Options.output_to () in
             FStar_Pervasives_Native.uu___is_Some uu___2) &&
              ((FStarC_List.length mllib) > Prims.int_one) in
          if uu___1
          then
            let uu___2 =
              let uu___3 =
                FStarC_Errors_Msg.text
                  "Cannot provide -o and extract multiple modules" in
              let uu___4 =
                let uu___5 =
                  FStarC_Errors_Msg.text
                    "Please use -o with a single module, or specify an output directory with --odir" in
                [uu___5] in
              uu___3 :: uu___4 in
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___2)
          else ());
         FStarC_List.iter
           (fun uu___1 ->
              match uu___1 with
              | (uu___2, mlmodule) ->
                  let uu___3 = mlmodule in
                  (match uu___3 with
                   | (p, uu___4) ->
                       let filename =
                         let basename =
                           let uu___5 =
                             FStarC_Extraction_ML_Util.flatten_mlpath p in
                           Prims.strcat uu___5 ext in
                         ofile basename in
                       let ml = printer mlmodule in
                       FStarC_Util.write_file filename ml)) mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.Plugin) ->
        let printer =
          if opt = (FStar_Pervasives_Native.Some FStarC_Options.FSharp)
          then FStarC_Extraction_ML_PrintFS.print_fs
          else FStarC_Extraction_ML_PrintML.print_ml in
        ((let uu___1 =
            (let uu___2 = FStarC_Options.output_to () in
             FStar_Pervasives_Native.uu___is_Some uu___2) &&
              ((FStarC_List.length mllib) > Prims.int_one) in
          if uu___1
          then
            let uu___2 =
              let uu___3 =
                FStarC_Errors_Msg.text
                  "Cannot provide -o and extract multiple modules" in
              let uu___4 =
                let uu___5 =
                  FStarC_Errors_Msg.text
                    "Please use -o with a single module, or specify an output directory with --odir" in
                [uu___5] in
              uu___3 :: uu___4 in
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___2)
          else ());
         FStarC_List.iter
           (fun uu___1 ->
              match uu___1 with
              | (uu___2, mlmodule) ->
                  let uu___3 = mlmodule in
                  (match uu___3 with
                   | (p, uu___4) ->
                       let filename =
                         let basename =
                           let uu___5 =
                             FStarC_Extraction_ML_Util.flatten_mlpath p in
                           Prims.strcat uu___5 ext in
                         ofile basename in
                       let ml = printer mlmodule in
                       FStarC_Util.write_file filename ml)) mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.PluginNoLib) ->
        let printer =
          if opt = (FStar_Pervasives_Native.Some FStarC_Options.FSharp)
          then FStarC_Extraction_ML_PrintFS.print_fs
          else FStarC_Extraction_ML_PrintML.print_ml in
        ((let uu___1 =
            (let uu___2 = FStarC_Options.output_to () in
             FStar_Pervasives_Native.uu___is_Some uu___2) &&
              ((FStarC_List.length mllib) > Prims.int_one) in
          if uu___1
          then
            let uu___2 =
              let uu___3 =
                FStarC_Errors_Msg.text
                  "Cannot provide -o and extract multiple modules" in
              let uu___4 =
                let uu___5 =
                  FStarC_Errors_Msg.text
                    "Please use -o with a single module, or specify an output directory with --odir" in
                [uu___5] in
              uu___3 :: uu___4 in
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___2)
          else ());
         FStarC_List.iter
           (fun uu___1 ->
              match uu___1 with
              | (uu___2, mlmodule) ->
                  let uu___3 = mlmodule in
                  (match uu___3 with
                   | (p, uu___4) ->
                       let filename =
                         let basename =
                           let uu___5 =
                             FStarC_Extraction_ML_Util.flatten_mlpath p in
                           Prims.strcat uu___5 ext in
                         ofile basename in
                       let ml = printer mlmodule in
                       FStarC_Util.write_file filename ml)) mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.Extension) ->
        ((let uu___1 =
            (let uu___2 = FStarC_Options.output_to () in
             FStar_Pervasives_Native.uu___is_Some uu___2) &&
              ((FStarC_List.length mllib) > Prims.int_one) in
          if uu___1
          then
            let uu___2 =
              let uu___3 =
                FStarC_Errors_Msg.text
                  "Cannot provide -o and extract multiple modules" in
              let uu___4 =
                let uu___5 =
                  FStarC_Errors_Msg.text
                    "Please use -o with a single module, or specify an output directory with --odir" in
                [uu___5] in
              uu___3 :: uu___4 in
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___2)
          else ());
         FStarC_List.iter
           (fun uu___1 ->
              match uu___1 with
              | (env, m) ->
                  let uu___2 = m in
                  (match uu___2 with
                   | (mname, modul) ->
                       let filename =
                         let basename =
                           let uu___3 =
                             FStarC_Extraction_ML_Util.flatten_mlpath mname in
                           Prims.strcat uu___3 ext in
                         ofile basename in
                       (match modul with
                        | FStar_Pervasives_Native.Some (uu___3, decls) ->
                            let bindings =
                              FStarC_Extraction_ML_UEnv.bindings_of_uenv env in
                            let deps =
                              let uu___4 =
                                FStarC_Extraction_ML_Syntax.string_of_mlpath
                                  mname in
                              FStarC_Parser_Dep.deps_of_modul dep_graph
                                uu___4 in
                            FStarC_Util.save_value_to_file filename
                              (deps, bindings, decls)
                        | FStar_Pervasives_Native.None ->
                            failwith
                              "Unexpected ml modul in Extension extraction mode")))
           mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.Krml) ->
        let programs =
          FStarC_List.collect
            (fun uu___ ->
               match uu___ with
               | (ue, m) -> FStarC_Extraction_Krml.translate ue [m]) mllib in
        let bin = (FStarC_Extraction_Krml.current_version, programs) in
        let oname =
          let uu___ = FStarC_Options.krmloutput () in
          match uu___ with
          | FStar_Pervasives_Native.Some fname -> fname
          | uu___1 ->
              (match programs with
               | (name, uu___2)::[] ->
                   FStarC_Find.prepend_output_dir (Prims.strcat name ext)
               | uu___2 ->
                   FStarC_Find.prepend_output_dir (Prims.strcat "out" ext)) in
        FStarC_Util.save_value_to_file oname bin
    | uu___ -> fail ()
  else ()
let needs_interleaving (intf : Prims.string) (impl : Prims.string) :
  Prims.bool=
  let m1 = FStarC_Parser_Dep.lowercase_module_name intf in
  let m2 = FStarC_Parser_Dep.lowercase_module_name impl in
  ((m1 = m2) &&
     (let uu___ = FStarC_Filepath.get_file_extension intf in
      FStarC_List.mem uu___ ["fsti"; "fsi"]))
    &&
    (let uu___ = FStarC_Filepath.get_file_extension impl in
     FStarC_List.mem uu___ ["fst"; "fs"])
let rec tc_one_file_internal (fly_deps : Prims.bool) (env : uenv)
  (interface_fn : Prims.string FStar_Pervasives_Native.option)
  (fn : Prims.string) :
  (FStarC_CheckedFiles.tc_result * FStarC_Extraction_ML_Syntax.mlmodule
    FStar_Pervasives_Native.option * uenv)=
  FStarC_Stats.record "tc_one_file"
    (fun uu___ ->
       FStarC_GenSym.reset_gensym ();
       (let restore_opts uu___2 =
          let uu___3 = FStarC_Options.restore_cmd_line_options true in () in
        let maybe_extract_mldefs tcmod env1 =
          let uu___2 = FStarC_Options.codegen () in
          match uu___2 with
          | FStar_Pervasives_Native.None ->
              (FStar_Pervasives_Native.None, Prims.int_zero)
          | FStar_Pervasives_Native.Some tgt ->
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStarC_Ident.string_of_lid
                      tcmod.FStarC_Syntax_Syntax.name in
                  FStarC_Options.should_extract uu___5 tgt in
                Prims.op_Negation uu___4 in
              if uu___3
              then (FStar_Pervasives_Native.None, Prims.int_zero)
              else
                FStarC_Timing.record_ms
                  (fun uu___5 ->
                     with_env env1
                       (fun env2 ->
                          let uu___6 =
                            FStarC_Extraction_ML_Modul.extract env2 tcmod in
                          match uu___6 with | (uu___7, defs) -> defs)) in
        let maybe_extract_ml_iface tcmod env1 =
          let uu___2 =
            let uu___3 = FStarC_Options.codegen () in
            uu___3 = FStar_Pervasives_Native.None in
          if uu___2
          then (env1, Prims.int_zero)
          else
            FStarC_Timing.record_ms
              (fun uu___4 ->
                 let uu___5 =
                   with_env env1
                     (fun env2 ->
                        FStarC_Extraction_ML_Modul.extract_iface env2 tcmod) in
                 match uu___5 with | (env2, uu___6) -> env2) in
        let tc_source_file uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Parser_Dep.module_name_of_file fn in
              FStar_Pervasives_Native.Some uu___5 in
            FStarC_Profiling.profile
              (fun uu___5 -> parse fly_deps env interface_fn fn) uu___4
              "FStarC.Universal.tc_source_file.parse" in
          match uu___3 with
          | (mname, fmod, env1) ->
              let check_mod uu___4 =
                let check env2 =
                  (let uu___6 =
                     let uu___7 = FStarC_Options.lax () in
                     Prims.op_Negation uu___7 in
                   if uu___6
                   then
                     FStarC_SMTEncoding_Z3.refresh
                       FStar_Pervasives_Native.None
                   else ());
                  (let uu___6 =
                     if fly_deps
                     then
                       let uu___7 = fmod in
                       match uu___7 with
                       | FStar_Pervasives.Inl ast_mod ->
                           fly_deps_check fn env2 ast_mod
                             (FStar_Pervasives_Native.uu___is_Some
                                interface_fn)
                     else
                       (let uu___8 = fmod in
                        match uu___8 with
                        | FStar_Pervasives.Inr mod1 ->
                            with_tcenv_of_env env2
                              (fun tcenv ->
                                 FStarC_TypeChecker_Tc.check_module tcenv
                                   mod1
                                   (FStar_Pervasives_Native.uu___is_Some
                                      interface_fn))) in
                   match uu___6 with
                   | (modul, env3) ->
                       (restore_opts ();
                        (let smt_decls =
                           let uu___8 =
                             let uu___9 = FStarC_Options.lax () in
                             Prims.op_Negation uu___9 in
                           if uu___8
                           then
                             let uu___9 =
                               FStarC_Extraction_ML_UEnv.tcenv_of_uenv env3 in
                             FStarC_SMTEncoding_Encode.encode_modul uu___9
                               modul
                           else ([], []) in
                         ((modul, smt_decls), env3)))) in
                let uu___5 =
                  let uu___6 =
                    let uu___7 = FStarC_Ident.string_of_lid mname in
                    FStar_Pervasives_Native.Some uu___7 in
                  FStarC_Profiling.profile (fun uu___7 -> check env1) uu___6
                    "FStarC.Universal.tc_source_file.check" in
                match uu___5 with
                | ((tcmod, smt_decls), env2) ->
                    let tc_time = Prims.int_zero in
                    let uu___6 = maybe_extract_mldefs tcmod env2 in
                    (match uu___6 with
                     | (extracted_defs, extract_time) ->
                         let uu___7 = maybe_extract_ml_iface tcmod env2 in
                         (match uu___7 with
                          | (env3, iface_extraction_time) ->
                              let pd =
                                let deps =
                                  let uu___8 =
                                    FStarC_Extraction_ML_UEnv.tcenv_of_uenv
                                      env3 in
                                  FStarC_TypeChecker_Env.dep_graph uu___8 in
                                match fmod with
                                | FStar_Pervasives.Inl ast_mod ->
                                    FStarC_Parser_Dep.parsing_data_of_modul
                                      deps fn
                                      (FStar_Pervasives_Native.Some ast_mod)
                                | FStar_Pervasives.Inr mod1 ->
                                    let pd1 =
                                      FStarC_Parser_Dep.parsing_data_of deps
                                        fn in
                                    let uu___8 =
                                      FStarC_Parser_Dep.deps_of deps fn in
                                    (pd1, uu___8) in
                              let mii =
                                let uu___8 =
                                  let uu___9 =
                                    FStarC_Extraction_ML_UEnv.tcenv_of_uenv
                                      env3 in
                                  uu___9.FStarC_TypeChecker_Env.dsenv in
                                FStarC_Syntax_DsEnv.inclusion_info uu___8
                                  mname in
                              (pd,
                                {
                                  FStarC_CheckedFiles.checked_module = tcmod;
                                  FStarC_CheckedFiles.mii = mii;
                                  FStarC_CheckedFiles.smt_decls = smt_decls;
                                  FStarC_CheckedFiles.tc_time = tc_time;
                                  FStarC_CheckedFiles.extraction_time =
                                    (extract_time + iface_extraction_time)
                                }, extracted_defs, env3))) in
              let uu___4 = FStarC_Parser_ParseIt.find_file fn in
              FStarC_SMTEncoding_Solver.with_hints_db uu___4 check_mod in
        let uu___2 =
          let uu___3 = FStarC_Options.cache_off () in
          Prims.op_Negation uu___3 in
        if uu___2
        then
          let r =
            let uu___3 = fly_deps && (FStarC_Options.should_check_file fn) in
            if uu___3
            then FStar_Pervasives_Native.None
            else
              (let uu___5 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env in
               FStarC_CheckedFiles.load_module_from_cache uu___5 fn) in
          let r1 =
            let uu___3 =
              (FStarC_Options.should_check_file fn) &&
                ((FStarC_Options.force ()) ||
                   ((let uu___4 = FStarC_Options.output_to () in
                     FStar_Pervasives_Native.uu___is_Some uu___4) &&
                      (let uu___4 = FStarC_Options.codegen () in
                       FStar_Pervasives_Native.uu___is_None uu___4))) in
            if uu___3 then FStar_Pervasives_Native.None else r in
          match r1 with
          | FStar_Pervasives_Native.None ->
              ((let uu___4 =
                  (let uu___5 = FStarC_Parser_Dep.module_name_of_file fn in
                   FStarC_Options.should_be_already_cached uu___5) &&
                    (let uu___5 = FStarC_Options.force () in
                     Prims.op_Negation uu___5) in
                if uu___4
                then
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        FStarC_Format.fmt1
                          "Expected %s to already be checked." fn in
                      FStarC_Errors_Msg.text uu___7 in
                    [uu___6] in
                  FStarC_Errors.raise_error0
                    FStarC_Errors_Codes.Error_AlreadyCachedAssertionFailure
                    ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic uu___5)
                else ());
               (let uu___5 =
                  ((let uu___6 = FStarC_Options.codegen () in
                    FStar_Pervasives_Native.uu___is_Some uu___6) &&
                     (FStarC_Options.cmi ()))
                    &&
                    (let uu___6 = FStarC_Options.force () in
                     Prims.op_Negation uu___6) in
                if uu___5
                then
                  let uu___6 =
                    let uu___7 =
                      FStarC_Errors_Msg.text
                        "Cross-module inlining expects all modules to be checked first." in
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          FStarC_Format.fmt1 "Module %s was not checked." fn in
                        FStarC_Errors_Msg.text uu___10 in
                      [uu___9] in
                    uu___7 :: uu___8 in
                  FStarC_Errors.raise_error0
                    FStarC_Errors_Codes.Error_AlreadyCachedAssertionFailure
                    ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic uu___6)
                else ());
               (let uu___5 = tc_source_file () in
                match uu___5 with
                | (parsing_data, tc_result, mllib, env1) ->
                    ((let uu___7 =
                        (let uu___8 = FStarC_Errors.get_err_count () in
                         uu___8 = Prims.int_zero) &&
                          ((FStarC_Options.lax ()) ||
                             (let uu___8 =
                                FStarC_Ident.string_of_lid
                                  (tc_result.FStarC_CheckedFiles.checked_module).FStarC_Syntax_Syntax.name in
                              FStarC_Options.should_verify uu___8)) in
                      if uu___7
                      then
                        let uu___8 =
                          FStarC_Extraction_ML_UEnv.tcenv_of_uenv env1 in
                        FStarC_CheckedFiles.store_module_to_cache uu___8 fn
                          parsing_data tc_result
                      else ());
                     (tc_result, mllib, env1))))
          | FStar_Pervasives_Native.Some tc_result ->
              let tcmod = tc_result.FStarC_CheckedFiles.checked_module in
              let smt_decls = tc_result.FStarC_CheckedFiles.smt_decls in
              ((let uu___4 =
                  let uu___5 =
                    FStarC_Ident.string_of_lid
                      tcmod.FStarC_Syntax_Syntax.name in
                  FStarC_Options.dump_module uu___5 in
                if uu___4
                then
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_modul
                      tcmod in
                  FStarC_Format.print1 "Module after type checking:\n%s\n"
                    uu___5
                else ());
               (let extend_tcenv tcmod1 tcenv =
                  let uu___4 =
                    let uu___5 =
                      FStarC_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                        tc_result.FStarC_CheckedFiles.mii
                        (FStarC_TypeChecker_Normalize.erase_universes tcenv) in
                    with_dsenv_of_tcenv tcenv uu___5 in
                  match uu___4 with
                  | (uu___5, tcenv1) ->
                      let env1 =
                        FStarC_TypeChecker_Tc.load_checked_module tcenv1
                          tcmod1 in
                      (restore_opts ();
                       (let uu___8 =
                          let uu___9 = FStarC_Options.lax () in
                          Prims.op_Negation uu___9 in
                        if uu___8
                        then
                          FStarC_SMTEncoding_Encode.encode_modul_from_cache
                            env1 tcmod1 smt_decls
                        else ());
                       ((), env1)) in
                let env1 =
                  FStarC_Profiling.profile
                    (fun uu___4 ->
                       let uu___5 =
                         with_tcenv_of_env env (extend_tcenv tcmod) in
                       FStar_Pervasives_Native.snd uu___5)
                    FStar_Pervasives_Native.None
                    "FStarC.Universal.extend_tcenv" in
                let mllib =
                  let uu___4 = FStarC_Options.codegen () in
                  match uu___4 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some tgt ->
                      let uu___5 =
                        (let uu___6 =
                           FStarC_Ident.string_of_lid
                             tcmod.FStarC_Syntax_Syntax.name in
                         FStarC_Options.should_extract uu___6 tgt) &&
                          ((Prims.op_Negation
                              tcmod.FStarC_Syntax_Syntax.is_interface)
                             || (tgt = FStarC_Options.Krml)) in
                      if uu___5
                      then
                        let uu___6 = maybe_extract_mldefs tcmod env1 in
                        (match uu___6 with
                         | (extracted_defs, _extraction_time) ->
                             extracted_defs)
                      else FStar_Pervasives_Native.None in
                let uu___4 = maybe_extract_ml_iface tcmod env1 in
                match uu___4 with | (env2, _time) -> (tc_result, mllib, env2)))
        else
          (let uu___4 = tc_source_file () in
           match uu___4 with
           | (uu___5, tc_result, mllib, env1) -> (tc_result, mllib, env1))))
and fly_deps_check (filename : Prims.string) (env : uenv)
  (ast_mod : FStarC_Parser_AST.modul) (iface_exists : Prims.bool) :
  (FStarC_Syntax_Syntax.modul * uenv)=
  let decls = FStarC_Parser_AST.decls_of_modul ast_mod in
  let mname =
    match decls with
    | { FStarC_Parser_AST.d = FStarC_Parser_AST.TopLevelModule lid;
        FStarC_Parser_AST.drange = uu___; FStarC_Parser_AST.quals = uu___1;
        FStarC_Parser_AST.attrs = uu___2;
        FStarC_Parser_AST.interleaved = uu___3;_}::rest -> lid
    | uu___ -> failwith "Impossible: first decl is not a module" in
  (let uu___1 = FStarC_Parser_Dep.debug_fly_deps () in
   if uu___1
   then
     let uu___2 =
       let uu___3 =
         FStarC_Class_PP.pp
           (FStarC_Class_PP.pp_list FStarC_Parser_AST.pretty_decl) decls in
       FStar_Pprint.render uu___3 in
     FStarC_Format.print1 "Before fly load deps: %s\n" uu___2
   else ());
  (let uu___2 =
     let uu___3 =
       let uu___4 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env in
       uu___4.FStarC_TypeChecker_Env.dsenv in
     FStarC_Syntax_DsEnv.dep_graph uu___3 in
   FStarC_Parser_Dep.populate_parsing_data filename ast_mod uu___2);
  (let is_interface = FStarC_Parser_Dep.is_interface filename in
   let uu___2 =
     FStarC_List.fold_left
       (fun uu___3 decl ->
          match uu___3 with
          | (mod1, env1) ->
              ((let uu___5 = FStarC_Parser_Dep.debug_fly_deps () in
                if uu___5
                then
                  let uu___6 =
                    let uu___7 =
                      FStarC_Class_PP.pp FStarC_Parser_AST.pretty_decl decl in
                    FStar_Pprint.render uu___7 in
                  FStarC_Format.print1 "fly_deps_check next decl: %s\n"
                    uu___6
                else ());
               (let uu___5 =
                  scan_and_load_fly_deps_internal filename env1
                    (FStar_Pervasives.Inr decl) in
                match uu___5 with
                | (env2, uu___6) ->
                    let uu___7 =
                      with_tcenv_of_env env2
                        (fun tcenv ->
                           let uu___8 =
                             tc_one_fragment is_interface mod1 tcenv
                               (FStar_Pervasives.Inr decl) in
                           match uu___8 with
                           | (mod2, tcenv1, uu___9) -> (mod2, tcenv1)) in
                    (match uu___7 with | (mod2, env3) -> (mod2, env3)))))
       (FStar_Pervasives_Native.None, env) decls in
   match uu___2 with
   | (mod1, env1) ->
       (if FStar_Pervasives_Native.uu___is_None mod1
        then failwith "Impossible"
        else ();
        (let uu___4 = mod1 in
         match uu___4 with
         | FStar_Pervasives_Native.Some mod2 ->
             let uu___5 =
               with_tcenv_of_env env1
                 (fun tcenv ->
                    let uu___6 =
                      FStarC_Syntax_DsEnv.finish_module_or_interface
                        tcenv.FStarC_TypeChecker_Env.dsenv mod2 in
                    match uu___6 with
                    | (dsenv, mod3) ->
                        let tcenv1 =
                          {
                            FStarC_TypeChecker_Env.solver =
                              (tcenv.FStarC_TypeChecker_Env.solver);
                            FStarC_TypeChecker_Env.range =
                              (tcenv.FStarC_TypeChecker_Env.range);
                            FStarC_TypeChecker_Env.curmodule =
                              (tcenv.FStarC_TypeChecker_Env.curmodule);
                            FStarC_TypeChecker_Env.gamma =
                              (tcenv.FStarC_TypeChecker_Env.gamma);
                            FStarC_TypeChecker_Env.gamma_sig =
                              (tcenv.FStarC_TypeChecker_Env.gamma_sig);
                            FStarC_TypeChecker_Env.gamma_cache =
                              (tcenv.FStarC_TypeChecker_Env.gamma_cache);
                            FStarC_TypeChecker_Env.modules =
                              (tcenv.FStarC_TypeChecker_Env.modules);
                            FStarC_TypeChecker_Env.expected_typ =
                              (tcenv.FStarC_TypeChecker_Env.expected_typ);
                            FStarC_TypeChecker_Env.sigtab =
                              (tcenv.FStarC_TypeChecker_Env.sigtab);
                            FStarC_TypeChecker_Env.attrtab =
                              (tcenv.FStarC_TypeChecker_Env.attrtab);
                            FStarC_TypeChecker_Env.instantiate_imp =
                              (tcenv.FStarC_TypeChecker_Env.instantiate_imp);
                            FStarC_TypeChecker_Env.effects =
                              (tcenv.FStarC_TypeChecker_Env.effects);
                            FStarC_TypeChecker_Env.generalize =
                              (tcenv.FStarC_TypeChecker_Env.generalize);
                            FStarC_TypeChecker_Env.letrecs =
                              (tcenv.FStarC_TypeChecker_Env.letrecs);
                            FStarC_TypeChecker_Env.top_level =
                              (tcenv.FStarC_TypeChecker_Env.top_level);
                            FStarC_TypeChecker_Env.check_uvars =
                              (tcenv.FStarC_TypeChecker_Env.check_uvars);
                            FStarC_TypeChecker_Env.use_eq_strict =
                              (tcenv.FStarC_TypeChecker_Env.use_eq_strict);
                            FStarC_TypeChecker_Env.is_iface =
                              (tcenv.FStarC_TypeChecker_Env.is_iface);
                            FStarC_TypeChecker_Env.admit =
                              (tcenv.FStarC_TypeChecker_Env.admit);
                            FStarC_TypeChecker_Env.phase1 =
                              (tcenv.FStarC_TypeChecker_Env.phase1);
                            FStarC_TypeChecker_Env.failhard =
                              (tcenv.FStarC_TypeChecker_Env.failhard);
                            FStarC_TypeChecker_Env.flychecking =
                              (tcenv.FStarC_TypeChecker_Env.flychecking);
                            FStarC_TypeChecker_Env.uvar_subtyping =
                              (tcenv.FStarC_TypeChecker_Env.uvar_subtyping);
                            FStarC_TypeChecker_Env.intactics =
                              (tcenv.FStarC_TypeChecker_Env.intactics);
                            FStarC_TypeChecker_Env.nocoerce =
                              (tcenv.FStarC_TypeChecker_Env.nocoerce);
                            FStarC_TypeChecker_Env.tc_term =
                              (tcenv.FStarC_TypeChecker_Env.tc_term);
                            FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                              (tcenv.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                            FStarC_TypeChecker_Env.universe_of =
                              (tcenv.FStarC_TypeChecker_Env.universe_of);
                            FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                              =
                              (tcenv.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                            FStarC_TypeChecker_Env.teq_nosmt_force =
                              (tcenv.FStarC_TypeChecker_Env.teq_nosmt_force);
                            FStarC_TypeChecker_Env.subtype_nosmt_force =
                              (tcenv.FStarC_TypeChecker_Env.subtype_nosmt_force);
                            FStarC_TypeChecker_Env.qtbl_name_and_index =
                              (tcenv.FStarC_TypeChecker_Env.qtbl_name_and_index);
                            FStarC_TypeChecker_Env.normalized_eff_names =
                              (tcenv.FStarC_TypeChecker_Env.normalized_eff_names);
                            FStarC_TypeChecker_Env.fv_delta_depths =
                              (tcenv.FStarC_TypeChecker_Env.fv_delta_depths);
                            FStarC_TypeChecker_Env.proof_ns =
                              (tcenv.FStarC_TypeChecker_Env.proof_ns);
                            FStarC_TypeChecker_Env.synth_hook =
                              (tcenv.FStarC_TypeChecker_Env.synth_hook);
                            FStarC_TypeChecker_Env.try_solve_implicits_hook =
                              (tcenv.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                            FStarC_TypeChecker_Env.splice =
                              (tcenv.FStarC_TypeChecker_Env.splice);
                            FStarC_TypeChecker_Env.mpreprocess =
                              (tcenv.FStarC_TypeChecker_Env.mpreprocess);
                            FStarC_TypeChecker_Env.postprocess =
                              (tcenv.FStarC_TypeChecker_Env.postprocess);
                            FStarC_TypeChecker_Env.identifier_info =
                              (tcenv.FStarC_TypeChecker_Env.identifier_info);
                            FStarC_TypeChecker_Env.tc_hooks =
                              (tcenv.FStarC_TypeChecker_Env.tc_hooks);
                            FStarC_TypeChecker_Env.dsenv = dsenv;
                            FStarC_TypeChecker_Env.nbe =
                              (tcenv.FStarC_TypeChecker_Env.nbe);
                            FStarC_TypeChecker_Env.strict_args_tab =
                              (tcenv.FStarC_TypeChecker_Env.strict_args_tab);
                            FStarC_TypeChecker_Env.erasable_types_tab =
                              (tcenv.FStarC_TypeChecker_Env.erasable_types_tab);
                            FStarC_TypeChecker_Env.enable_defer_to_tac =
                              (tcenv.FStarC_TypeChecker_Env.enable_defer_to_tac);
                            FStarC_TypeChecker_Env.unif_allow_ref_guards =
                              (tcenv.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                            FStarC_TypeChecker_Env.erase_erasable_args =
                              (tcenv.FStarC_TypeChecker_Env.erase_erasable_args);
                            FStarC_TypeChecker_Env.core_check =
                              (tcenv.FStarC_TypeChecker_Env.core_check);
                            FStarC_TypeChecker_Env.missing_decl =
                              (tcenv.FStarC_TypeChecker_Env.missing_decl)
                          } in
                        FStarC_TypeChecker_Tc.finish_partial_modul false
                          false iface_exists tcenv1 mod3) in
             (match uu___5 with | (mod3, env2) -> (mod3, env2)))))
and scan_and_load_fly_deps_internal (filename : Prims.string) (env : uenv)
  (frag_or_decl :
    ((FStarC_Parser_ParseIt.input_frag * lang_decls_t),
      FStarC_Parser_AST.decl) FStar_Pervasives.either)
  : (uenv * Prims.string Prims.list)=
  let load_fly_deps env1 filenames =
    let run_load_tasks env2 filenames1 =
      let uu___ = tc_fold_interleave false ([], [], env2) filenames1 in
      match uu___ with | (uu___1, uu___2, env3) -> env3 in
    let uu___ =
      FStarC_Extraction_ML_UEnv.with_restored_tc_scope env1
        (fun env2 ->
           let uu___1 = run_load_tasks env2 filenames in ((), uu___1)) in
    match uu___ with
    | (uu___1, env2) ->
        ((let uu___3 = FStarC_Parser_Dep.debug_fly_deps () in
          if uu___3
          then
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env2 in
                uu___6.FStarC_TypeChecker_Env.dsenv in
              FStarC_Class_Show.show FStarC_Syntax_DsEnv.showable_env uu___5 in
            FStarC_Format.print1 "After fly load deps: %s\n" uu___4
          else ());
         env2) in
  let scan_fragment_deps env1 frag_or_decl1 =
    let deps =
      FStarC_Syntax_DsEnv.dep_graph env1.FStarC_TypeChecker_Env.dsenv in
    let deps1 = FStarC_Parser_Dep.copy_deps deps in
    let env2 =
      let uu___ =
        FStarC_Syntax_DsEnv.set_dep_graph env1.FStarC_TypeChecker_Env.dsenv
          deps1 in
      {
        FStarC_TypeChecker_Env.solver = (env1.FStarC_TypeChecker_Env.solver);
        FStarC_TypeChecker_Env.range = (env1.FStarC_TypeChecker_Env.range);
        FStarC_TypeChecker_Env.curmodule =
          (env1.FStarC_TypeChecker_Env.curmodule);
        FStarC_TypeChecker_Env.gamma = (env1.FStarC_TypeChecker_Env.gamma);
        FStarC_TypeChecker_Env.gamma_sig =
          (env1.FStarC_TypeChecker_Env.gamma_sig);
        FStarC_TypeChecker_Env.gamma_cache =
          (env1.FStarC_TypeChecker_Env.gamma_cache);
        FStarC_TypeChecker_Env.modules =
          (env1.FStarC_TypeChecker_Env.modules);
        FStarC_TypeChecker_Env.expected_typ =
          (env1.FStarC_TypeChecker_Env.expected_typ);
        FStarC_TypeChecker_Env.sigtab = (env1.FStarC_TypeChecker_Env.sigtab);
        FStarC_TypeChecker_Env.attrtab =
          (env1.FStarC_TypeChecker_Env.attrtab);
        FStarC_TypeChecker_Env.instantiate_imp =
          (env1.FStarC_TypeChecker_Env.instantiate_imp);
        FStarC_TypeChecker_Env.effects =
          (env1.FStarC_TypeChecker_Env.effects);
        FStarC_TypeChecker_Env.generalize =
          (env1.FStarC_TypeChecker_Env.generalize);
        FStarC_TypeChecker_Env.letrecs =
          (env1.FStarC_TypeChecker_Env.letrecs);
        FStarC_TypeChecker_Env.top_level =
          (env1.FStarC_TypeChecker_Env.top_level);
        FStarC_TypeChecker_Env.check_uvars =
          (env1.FStarC_TypeChecker_Env.check_uvars);
        FStarC_TypeChecker_Env.use_eq_strict =
          (env1.FStarC_TypeChecker_Env.use_eq_strict);
        FStarC_TypeChecker_Env.is_iface =
          (env1.FStarC_TypeChecker_Env.is_iface);
        FStarC_TypeChecker_Env.admit = (env1.FStarC_TypeChecker_Env.admit);
        FStarC_TypeChecker_Env.phase1 = (env1.FStarC_TypeChecker_Env.phase1);
        FStarC_TypeChecker_Env.failhard =
          (env1.FStarC_TypeChecker_Env.failhard);
        FStarC_TypeChecker_Env.flychecking =
          (env1.FStarC_TypeChecker_Env.flychecking);
        FStarC_TypeChecker_Env.uvar_subtyping =
          (env1.FStarC_TypeChecker_Env.uvar_subtyping);
        FStarC_TypeChecker_Env.intactics =
          (env1.FStarC_TypeChecker_Env.intactics);
        FStarC_TypeChecker_Env.nocoerce =
          (env1.FStarC_TypeChecker_Env.nocoerce);
        FStarC_TypeChecker_Env.tc_term =
          (env1.FStarC_TypeChecker_Env.tc_term);
        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
          (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStarC_TypeChecker_Env.universe_of =
          (env1.FStarC_TypeChecker_Env.universe_of);
        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStarC_TypeChecker_Env.teq_nosmt_force =
          (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
        FStarC_TypeChecker_Env.subtype_nosmt_force =
          (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
        FStarC_TypeChecker_Env.qtbl_name_and_index =
          (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
        FStarC_TypeChecker_Env.normalized_eff_names =
          (env1.FStarC_TypeChecker_Env.normalized_eff_names);
        FStarC_TypeChecker_Env.fv_delta_depths =
          (env1.FStarC_TypeChecker_Env.fv_delta_depths);
        FStarC_TypeChecker_Env.proof_ns =
          (env1.FStarC_TypeChecker_Env.proof_ns);
        FStarC_TypeChecker_Env.synth_hook =
          (env1.FStarC_TypeChecker_Env.synth_hook);
        FStarC_TypeChecker_Env.try_solve_implicits_hook =
          (env1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
        FStarC_TypeChecker_Env.splice = (env1.FStarC_TypeChecker_Env.splice);
        FStarC_TypeChecker_Env.mpreprocess =
          (env1.FStarC_TypeChecker_Env.mpreprocess);
        FStarC_TypeChecker_Env.postprocess =
          (env1.FStarC_TypeChecker_Env.postprocess);
        FStarC_TypeChecker_Env.identifier_info =
          (env1.FStarC_TypeChecker_Env.identifier_info);
        FStarC_TypeChecker_Env.tc_hooks =
          (env1.FStarC_TypeChecker_Env.tc_hooks);
        FStarC_TypeChecker_Env.dsenv = uu___;
        FStarC_TypeChecker_Env.nbe = (env1.FStarC_TypeChecker_Env.nbe);
        FStarC_TypeChecker_Env.strict_args_tab =
          (env1.FStarC_TypeChecker_Env.strict_args_tab);
        FStarC_TypeChecker_Env.erasable_types_tab =
          (env1.FStarC_TypeChecker_Env.erasable_types_tab);
        FStarC_TypeChecker_Env.enable_defer_to_tac =
          (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
        FStarC_TypeChecker_Env.unif_allow_ref_guards =
          (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
        FStarC_TypeChecker_Env.erase_erasable_args =
          (env1.FStarC_TypeChecker_Env.erase_erasable_args);
        FStarC_TypeChecker_Env.core_check =
          (env1.FStarC_TypeChecker_Env.core_check);
        FStarC_TypeChecker_Env.missing_decl =
          (env1.FStarC_TypeChecker_Env.missing_decl)
      } in
    let decls =
      match frag_or_decl1 with
      | FStar_Pervasives.Inl (frag, lang_decls) ->
          let dfrag = parse_frag frag lang_decls in
          (match dfrag with
           | FStarC_Parser_Driver.Empty -> []
           | FStarC_Parser_Driver.Decls [] -> []
           | FStarC_Parser_Driver.Modul ast_modul ->
               FStarC_Parser_AST.decls_of_modul ast_modul
           | FStarC_Parser_Driver.Decls decls1 -> decls1)
      | FStar_Pervasives.Inr d -> [d] in
    let filenames_to_load =
      let uu___ =
        FStarC_Syntax_DsEnv.parsing_data_for_scope
          env2.FStarC_TypeChecker_Env.dsenv in
      FStarC_Parser_Dep.collect_deps_of_decl deps1 filename decls uu___
        FStarC_CheckedFiles.load_parsing_data_from_cache in
    (let uu___1 = FStarC_Parser_Dep.debug_fly_deps () in
     if uu___1
     then
       ((let uu___3 =
           let uu___4 = FStarC_Parser_Dep.all_files deps1 in
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
             uu___4 in
         FStarC_Format.print1 "Initial files loaded: %s\n" uu___3);
        (let uu___4 =
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_list FStarC_Parser_AST.showable_decl)
             decls in
         FStarC_Format.print1 "Decls scanned: %s\n" uu___4);
        (let uu___4 =
           FStarC_Class_Show.show
             (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
             filenames_to_load in
         FStarC_Format.print1 "Additional files to load: %s\n" uu___4))
     else ());
    (let filenames =
       FStarC_List.filter (fun fn -> fn <> filename)
         (FStarC_List.rev filenames_to_load) in
     FStarC_List.iter
       (fun fn ->
          let uu___2 =
            FStarC_List.existsb
              (fun m ->
                 let uu___3 = FStarC_Parser_Dep.module_name_of_file fn in
                 let uu___4 =
                   FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name in
                 uu___3 = uu___4) env2.FStarC_TypeChecker_Env.modules in
          if uu___2
          then
            let uu___3 = FStarC_TypeChecker_Env.get_range env2 in
            let uu___4 =
              let uu___5 =
                FStarC_Errors_Msg.text
                  "Friend dependences must be declared as the first dependence on a module." in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 = FStarC_Parser_Dep.module_name_of_file fn in
                    FStarC_Format.fmt1
                      "A non-friend dependence was already found on module %s."
                      uu___9 in
                  FStarC_Errors_Msg.text uu___8 in
                [uu___7] in
              uu___5 :: uu___6 in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
              uu___3 FStarC_Errors_Codes.Fatal_CyclicDependence ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___4)
          else ()) filenames;
     (filenames, env2)) in
  let uu___ =
    with_tcenv_of_env env
      (fun tcenv -> scan_fragment_deps tcenv frag_or_decl) in
  match uu___ with
  | (filenames, env1) ->
      let env2 = load_fly_deps env1 filenames in (env2, filenames)
and tc_one_file_from_remaining (fly_deps : Prims.bool)
  (remaining : Prims.string Prims.list) (env : uenv) :
  (Prims.string Prims.list * FStarC_CheckedFiles.tc_result *
    FStarC_Extraction_ML_Syntax.mlmodule FStar_Pervasives_Native.option *
    uenv)=
  let uu___ =
    match remaining with
    | intf::impl::remaining1 when needs_interleaving intf impl ->
        let uu___1 =
          tc_one_file_internal fly_deps env
            (FStar_Pervasives_Native.Some intf) impl in
        (match uu___1 with
         | (m, mllib, env1) -> (remaining1, (m, mllib, env1)))
    | intf_or_impl::remaining1 ->
        let uu___1 =
          tc_one_file_internal fly_deps env FStar_Pervasives_Native.None
            intf_or_impl in
        (match uu___1 with
         | (m, mllib, env1) -> (remaining1, (m, mllib, env1)))
    | [] -> failwith "Impossible: Empty remaining modules" in
  match uu___ with
  | (remaining1, (nmods, mllib, env1)) -> (remaining1, nmods, mllib, env1)
and tc_fold_interleave (fly_deps : Prims.bool)
  (acc :
    (FStarC_CheckedFiles.tc_result Prims.list * (uenv *
      FStarC_Extraction_ML_Syntax.mlmodule) Prims.list * uenv))
  (remaining : Prims.string Prims.list) :
  (FStarC_CheckedFiles.tc_result Prims.list * (uenv *
    FStarC_Extraction_ML_Syntax.mlmodule) Prims.list * uenv)=
  let as_list env mllib =
    match mllib with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some mllib1 -> [(env, mllib1)] in
  match remaining with
  | [] -> acc
  | uu___ ->
      let uu___1 = acc in
      (match uu___1 with
       | (mods, mllibs, env_before) ->
           let uu___2 =
             tc_one_file_from_remaining fly_deps remaining env_before in
           (match uu___2 with
            | (remaining1, nmod, mllib, env) ->
                ((let uu___4 =
                    let uu___5 = FStarC_Options.profile_group_by_decl () in
                    Prims.op_Negation uu___5 in
                  if uu___4
                  then
                    let uu___5 =
                      FStarC_Ident.string_of_lid
                        (nmod.FStarC_CheckedFiles.checked_module).FStarC_Syntax_Syntax.name in
                    FStarC_Profiling.report_and_clear uu___5
                  else ());
                 tc_fold_interleave fly_deps
                   ((FStarC_List.op_At mods [nmod]),
                     (FStarC_List.op_At mllibs (as_list env mllib)), env)
                   remaining1)))
let load_file (env : FStarC_TypeChecker_Env.env_t)
  (interface_fn : Prims.string FStar_Pervasives_Native.option)
  (fn : Prims.string) : FStarC_TypeChecker_Env.env_t=
  let env1 = env_of_tcenv env in
  let uu___ = tc_one_file_internal false env1 interface_fn fn in
  match uu___ with
  | (tc_result, uu___1, env2) -> FStarC_Extraction_ML_UEnv.tcenv_of_uenv env2
let scan_and_load_fly_deps (filename : Prims.string)
  (env : FStarC_TypeChecker_Env.env_t)
  (input :
    ((FStarC_Parser_ParseIt.input_frag * lang_decls_t),
      FStarC_Parser_AST.decl) FStar_Pervasives.either)
  : (FStarC_TypeChecker_Env.env * Prims.string Prims.list)=
  let uu___ =
    let uu___1 = FStarC_Extraction_ML_UEnv.new_uenv env in
    scan_and_load_fly_deps_internal filename uu___1 input in
  match uu___ with
  | (uenv1, files) ->
      let uu___1 = FStarC_Extraction_ML_UEnv.tcenv_of_uenv uenv1 in
      (uu___1, files)
let load_fly_deps_and_tc_one_fragment (filename : Prims.string)
  (is_interface : Prims.bool)
  (mod1 : FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  (tcenv : FStarC_TypeChecker_Env.env_t)
  (frag_or_decl :
    ((FStarC_Parser_ParseIt.input_frag * lang_decls_t),
      FStarC_Parser_AST.decl) FStar_Pervasives.either)
  :
  (FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option *
    FStarC_TypeChecker_Env.env * lang_decls_t * Prims.string Prims.list)=
  let tcenv1 =
    let uu___ =
      ((FStarC_Options.interactive ()) &&
         (let uu___1 =
            FStarC_Syntax_DsEnv.iface_interleaving_init
              tcenv.FStarC_TypeChecker_Env.dsenv in
          Prims.op_Negation uu___1))
        && (FStarC_Parser_Dep.is_implementation filename) in
    if uu___
    then
      let deps =
        FStarC_Syntax_DsEnv.dep_graph tcenv.FStarC_TypeChecker_Env.dsenv in
      let m = FStarC_Parser_Dep.lowercase_module_name filename in
      let uu___1 = FStarC_Parser_Dep.interface_of deps m in
      match uu___1 with
      | FStar_Pervasives_Native.None -> tcenv
      | FStar_Pervasives_Native.Some fn -> load_interface_decls tcenv fn
    else tcenv in
  let ast_decls =
    match frag_or_decl with
    | FStar_Pervasives.Inl (frag, lang_decls) ->
        let dfrag = parse_frag frag lang_decls in
        (match dfrag with
         | FStarC_Parser_Driver.Empty -> []
         | FStarC_Parser_Driver.Decls [] -> []
         | FStarC_Parser_Driver.Modul ast_modul ->
             FStarC_Parser_AST.decls_of_modul ast_modul
         | FStarC_Parser_Driver.Decls decls -> decls)
    | FStar_Pervasives.Inr d -> [d] in
  let uu___ =
    FStarC_Util.fold_map
      (fun env a_decl ->
         let uu___1 =
           let uu___2 =
             FStarC_ToSyntax_Interleave.prefix_with_interface_decls a_decl in
           with_dsenv_of_tcenv env uu___2 in
         match uu___1 with | (decls, env1) -> (env1, decls)) tcenv1 ast_decls in
  match uu___ with
  | (tcenv2, interleaved_decls) ->
      let uu___1 =
        FStarC_Util.fold_map
          (fun uu___2 a_decl ->
             match uu___2 with
             | (tcenv3, curmod) ->
                 let uu___3 =
                   scan_and_load_fly_deps filename tcenv3
                     (FStar_Pervasives.Inr a_decl) in
                 (match uu___3 with
                  | (tcenv4, filenames) ->
                      let uu___4 =
                        tc_one_fragment is_interface curmod tcenv4
                          (FStar_Pervasives.Inr a_decl) in
                      (match uu___4 with
                       | (curmod1, tcenv5, langs) ->
                           ((tcenv5, curmod1), (langs, filenames)))))
          (tcenv2, mod1) (FStarC_List.flatten interleaved_decls) in
      (match uu___1 with
       | ((tcenv3, curmod), langs_filenames) ->
           let uu___2 = FStarC_List.unzip langs_filenames in
           (match uu___2 with
            | (langs_l, filenames_l) ->
                (curmod, tcenv3, (FStarC_List.flatten langs_l),
                  (FStarC_List.flatten filenames_l))))
let init_env (deps : FStarC_Parser_Dep.deps) : FStarC_TypeChecker_Env.env=
  let solver =
    let uu___ = FStarC_Options.lax () in
    if uu___
    then FStarC_SMTEncoding_Solver.dummy
    else
      {
        FStarC_TypeChecker_Env.init =
          (FStarC_SMTEncoding_Solver.solver.FStarC_TypeChecker_Env.init);
        FStarC_TypeChecker_Env.snapshot =
          (FStarC_SMTEncoding_Solver.solver.FStarC_TypeChecker_Env.snapshot);
        FStarC_TypeChecker_Env.rollback =
          (FStarC_SMTEncoding_Solver.solver.FStarC_TypeChecker_Env.rollback);
        FStarC_TypeChecker_Env.encode_sig =
          (FStarC_SMTEncoding_Solver.solver.FStarC_TypeChecker_Env.encode_sig);
        FStarC_TypeChecker_Env.preprocess = FStarC_Tactics_Hooks.preprocess;
        FStarC_TypeChecker_Env.spinoff_strictly_positive_goals =
          (FStar_Pervasives_Native.Some
             FStarC_Tactics_Hooks.spinoff_strictly_positive_goals);
        FStarC_TypeChecker_Env.handle_smt_goal =
          FStarC_Tactics_Hooks.handle_smt_goal;
        FStarC_TypeChecker_Env.solve =
          (FStarC_SMTEncoding_Solver.solver.FStarC_TypeChecker_Env.solve);
        FStarC_TypeChecker_Env.solve_sync =
          (FStarC_SMTEncoding_Solver.solver.FStarC_TypeChecker_Env.solve_sync);
        FStarC_TypeChecker_Env.finish =
          (FStarC_SMTEncoding_Solver.solver.FStarC_TypeChecker_Env.finish);
        FStarC_TypeChecker_Env.refresh =
          (FStarC_SMTEncoding_Solver.solver.FStarC_TypeChecker_Env.refresh)
      } in
  let env =
    let uu___ =
      let uu___1 = FStarC_Tactics_Interpreter.primitive_steps () in
      FStarC_TypeChecker_NBE.normalize uu___1 in
    FStarC_TypeChecker_Env.initial_env deps FStarC_TypeChecker_TcTerm.tc_term
      FStarC_TypeChecker_TcTerm.typeof_tot_or_gtot_term
      FStarC_TypeChecker_TcTerm.typeof_tot_or_gtot_term_fastpath
      FStarC_TypeChecker_TcTerm.universe_of
      FStarC_TypeChecker_Rel.teq_nosmt_force
      FStarC_TypeChecker_Rel.subtype_nosmt_force solver
      FStarC_Parser_Const.prims_lid uu___ core_check in
  let env1 =
    {
      FStarC_TypeChecker_Env.solver = (env.FStarC_TypeChecker_Env.solver);
      FStarC_TypeChecker_Env.range = (env.FStarC_TypeChecker_Env.range);
      FStarC_TypeChecker_Env.curmodule =
        (env.FStarC_TypeChecker_Env.curmodule);
      FStarC_TypeChecker_Env.gamma = (env.FStarC_TypeChecker_Env.gamma);
      FStarC_TypeChecker_Env.gamma_sig =
        (env.FStarC_TypeChecker_Env.gamma_sig);
      FStarC_TypeChecker_Env.gamma_cache =
        (env.FStarC_TypeChecker_Env.gamma_cache);
      FStarC_TypeChecker_Env.modules = (env.FStarC_TypeChecker_Env.modules);
      FStarC_TypeChecker_Env.expected_typ =
        (env.FStarC_TypeChecker_Env.expected_typ);
      FStarC_TypeChecker_Env.sigtab = (env.FStarC_TypeChecker_Env.sigtab);
      FStarC_TypeChecker_Env.attrtab = (env.FStarC_TypeChecker_Env.attrtab);
      FStarC_TypeChecker_Env.instantiate_imp =
        (env.FStarC_TypeChecker_Env.instantiate_imp);
      FStarC_TypeChecker_Env.effects = (env.FStarC_TypeChecker_Env.effects);
      FStarC_TypeChecker_Env.generalize =
        (env.FStarC_TypeChecker_Env.generalize);
      FStarC_TypeChecker_Env.letrecs = (env.FStarC_TypeChecker_Env.letrecs);
      FStarC_TypeChecker_Env.top_level =
        (env.FStarC_TypeChecker_Env.top_level);
      FStarC_TypeChecker_Env.check_uvars =
        (env.FStarC_TypeChecker_Env.check_uvars);
      FStarC_TypeChecker_Env.use_eq_strict =
        (env.FStarC_TypeChecker_Env.use_eq_strict);
      FStarC_TypeChecker_Env.is_iface = (env.FStarC_TypeChecker_Env.is_iface);
      FStarC_TypeChecker_Env.admit = (env.FStarC_TypeChecker_Env.admit);
      FStarC_TypeChecker_Env.phase1 = (env.FStarC_TypeChecker_Env.phase1);
      FStarC_TypeChecker_Env.failhard = (env.FStarC_TypeChecker_Env.failhard);
      FStarC_TypeChecker_Env.flychecking =
        (env.FStarC_TypeChecker_Env.flychecking);
      FStarC_TypeChecker_Env.uvar_subtyping =
        (env.FStarC_TypeChecker_Env.uvar_subtyping);
      FStarC_TypeChecker_Env.intactics =
        (env.FStarC_TypeChecker_Env.intactics);
      FStarC_TypeChecker_Env.nocoerce = (env.FStarC_TypeChecker_Env.nocoerce);
      FStarC_TypeChecker_Env.tc_term = (env.FStarC_TypeChecker_Env.tc_term);
      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
        (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
      FStarC_TypeChecker_Env.universe_of =
        (env.FStarC_TypeChecker_Env.universe_of);
      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
        (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
      FStarC_TypeChecker_Env.teq_nosmt_force =
        (env.FStarC_TypeChecker_Env.teq_nosmt_force);
      FStarC_TypeChecker_Env.subtype_nosmt_force =
        (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
      FStarC_TypeChecker_Env.qtbl_name_and_index =
        (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
      FStarC_TypeChecker_Env.normalized_eff_names =
        (env.FStarC_TypeChecker_Env.normalized_eff_names);
      FStarC_TypeChecker_Env.fv_delta_depths =
        (env.FStarC_TypeChecker_Env.fv_delta_depths);
      FStarC_TypeChecker_Env.proof_ns = (env.FStarC_TypeChecker_Env.proof_ns);
      FStarC_TypeChecker_Env.synth_hook = FStarC_Tactics_Hooks.synthesize;
      FStarC_TypeChecker_Env.try_solve_implicits_hook =
        (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
      FStarC_TypeChecker_Env.splice = (env.FStarC_TypeChecker_Env.splice);
      FStarC_TypeChecker_Env.mpreprocess =
        (env.FStarC_TypeChecker_Env.mpreprocess);
      FStarC_TypeChecker_Env.postprocess =
        (env.FStarC_TypeChecker_Env.postprocess);
      FStarC_TypeChecker_Env.identifier_info =
        (env.FStarC_TypeChecker_Env.identifier_info);
      FStarC_TypeChecker_Env.tc_hooks = (env.FStarC_TypeChecker_Env.tc_hooks);
      FStarC_TypeChecker_Env.dsenv = (env.FStarC_TypeChecker_Env.dsenv);
      FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
      FStarC_TypeChecker_Env.strict_args_tab =
        (env.FStarC_TypeChecker_Env.strict_args_tab);
      FStarC_TypeChecker_Env.erasable_types_tab =
        (env.FStarC_TypeChecker_Env.erasable_types_tab);
      FStarC_TypeChecker_Env.enable_defer_to_tac =
        (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
      FStarC_TypeChecker_Env.unif_allow_ref_guards =
        (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
      FStarC_TypeChecker_Env.erase_erasable_args =
        (env.FStarC_TypeChecker_Env.erase_erasable_args);
      FStarC_TypeChecker_Env.core_check =
        (env.FStarC_TypeChecker_Env.core_check);
      FStarC_TypeChecker_Env.missing_decl =
        (env.FStarC_TypeChecker_Env.missing_decl)
    } in
  let env2 =
    {
      FStarC_TypeChecker_Env.solver = (env1.FStarC_TypeChecker_Env.solver);
      FStarC_TypeChecker_Env.range = (env1.FStarC_TypeChecker_Env.range);
      FStarC_TypeChecker_Env.curmodule =
        (env1.FStarC_TypeChecker_Env.curmodule);
      FStarC_TypeChecker_Env.gamma = (env1.FStarC_TypeChecker_Env.gamma);
      FStarC_TypeChecker_Env.gamma_sig =
        (env1.FStarC_TypeChecker_Env.gamma_sig);
      FStarC_TypeChecker_Env.gamma_cache =
        (env1.FStarC_TypeChecker_Env.gamma_cache);
      FStarC_TypeChecker_Env.modules = (env1.FStarC_TypeChecker_Env.modules);
      FStarC_TypeChecker_Env.expected_typ =
        (env1.FStarC_TypeChecker_Env.expected_typ);
      FStarC_TypeChecker_Env.sigtab = (env1.FStarC_TypeChecker_Env.sigtab);
      FStarC_TypeChecker_Env.attrtab = (env1.FStarC_TypeChecker_Env.attrtab);
      FStarC_TypeChecker_Env.instantiate_imp =
        (env1.FStarC_TypeChecker_Env.instantiate_imp);
      FStarC_TypeChecker_Env.effects = (env1.FStarC_TypeChecker_Env.effects);
      FStarC_TypeChecker_Env.generalize =
        (env1.FStarC_TypeChecker_Env.generalize);
      FStarC_TypeChecker_Env.letrecs = (env1.FStarC_TypeChecker_Env.letrecs);
      FStarC_TypeChecker_Env.top_level =
        (env1.FStarC_TypeChecker_Env.top_level);
      FStarC_TypeChecker_Env.check_uvars =
        (env1.FStarC_TypeChecker_Env.check_uvars);
      FStarC_TypeChecker_Env.use_eq_strict =
        (env1.FStarC_TypeChecker_Env.use_eq_strict);
      FStarC_TypeChecker_Env.is_iface =
        (env1.FStarC_TypeChecker_Env.is_iface);
      FStarC_TypeChecker_Env.admit = (env1.FStarC_TypeChecker_Env.admit);
      FStarC_TypeChecker_Env.phase1 = (env1.FStarC_TypeChecker_Env.phase1);
      FStarC_TypeChecker_Env.failhard =
        (env1.FStarC_TypeChecker_Env.failhard);
      FStarC_TypeChecker_Env.flychecking =
        (env1.FStarC_TypeChecker_Env.flychecking);
      FStarC_TypeChecker_Env.uvar_subtyping =
        (env1.FStarC_TypeChecker_Env.uvar_subtyping);
      FStarC_TypeChecker_Env.intactics =
        (env1.FStarC_TypeChecker_Env.intactics);
      FStarC_TypeChecker_Env.nocoerce =
        (env1.FStarC_TypeChecker_Env.nocoerce);
      FStarC_TypeChecker_Env.tc_term = (env1.FStarC_TypeChecker_Env.tc_term);
      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
        (env1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
      FStarC_TypeChecker_Env.universe_of =
        (env1.FStarC_TypeChecker_Env.universe_of);
      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
        (env1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
      FStarC_TypeChecker_Env.teq_nosmt_force =
        (env1.FStarC_TypeChecker_Env.teq_nosmt_force);
      FStarC_TypeChecker_Env.subtype_nosmt_force =
        (env1.FStarC_TypeChecker_Env.subtype_nosmt_force);
      FStarC_TypeChecker_Env.qtbl_name_and_index =
        (env1.FStarC_TypeChecker_Env.qtbl_name_and_index);
      FStarC_TypeChecker_Env.normalized_eff_names =
        (env1.FStarC_TypeChecker_Env.normalized_eff_names);
      FStarC_TypeChecker_Env.fv_delta_depths =
        (env1.FStarC_TypeChecker_Env.fv_delta_depths);
      FStarC_TypeChecker_Env.proof_ns =
        (env1.FStarC_TypeChecker_Env.proof_ns);
      FStarC_TypeChecker_Env.synth_hook =
        (env1.FStarC_TypeChecker_Env.synth_hook);
      FStarC_TypeChecker_Env.try_solve_implicits_hook =
        FStarC_Tactics_Hooks.solve_implicits;
      FStarC_TypeChecker_Env.splice = (env1.FStarC_TypeChecker_Env.splice);
      FStarC_TypeChecker_Env.mpreprocess =
        (env1.FStarC_TypeChecker_Env.mpreprocess);
      FStarC_TypeChecker_Env.postprocess =
        (env1.FStarC_TypeChecker_Env.postprocess);
      FStarC_TypeChecker_Env.identifier_info =
        (env1.FStarC_TypeChecker_Env.identifier_info);
      FStarC_TypeChecker_Env.tc_hooks =
        (env1.FStarC_TypeChecker_Env.tc_hooks);
      FStarC_TypeChecker_Env.dsenv = (env1.FStarC_TypeChecker_Env.dsenv);
      FStarC_TypeChecker_Env.nbe = (env1.FStarC_TypeChecker_Env.nbe);
      FStarC_TypeChecker_Env.strict_args_tab =
        (env1.FStarC_TypeChecker_Env.strict_args_tab);
      FStarC_TypeChecker_Env.erasable_types_tab =
        (env1.FStarC_TypeChecker_Env.erasable_types_tab);
      FStarC_TypeChecker_Env.enable_defer_to_tac =
        (env1.FStarC_TypeChecker_Env.enable_defer_to_tac);
      FStarC_TypeChecker_Env.unif_allow_ref_guards =
        (env1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
      FStarC_TypeChecker_Env.erase_erasable_args =
        (env1.FStarC_TypeChecker_Env.erase_erasable_args);
      FStarC_TypeChecker_Env.core_check =
        (env1.FStarC_TypeChecker_Env.core_check);
      FStarC_TypeChecker_Env.missing_decl =
        (env1.FStarC_TypeChecker_Env.missing_decl)
    } in
  let env3 =
    {
      FStarC_TypeChecker_Env.solver = (env2.FStarC_TypeChecker_Env.solver);
      FStarC_TypeChecker_Env.range = (env2.FStarC_TypeChecker_Env.range);
      FStarC_TypeChecker_Env.curmodule =
        (env2.FStarC_TypeChecker_Env.curmodule);
      FStarC_TypeChecker_Env.gamma = (env2.FStarC_TypeChecker_Env.gamma);
      FStarC_TypeChecker_Env.gamma_sig =
        (env2.FStarC_TypeChecker_Env.gamma_sig);
      FStarC_TypeChecker_Env.gamma_cache =
        (env2.FStarC_TypeChecker_Env.gamma_cache);
      FStarC_TypeChecker_Env.modules = (env2.FStarC_TypeChecker_Env.modules);
      FStarC_TypeChecker_Env.expected_typ =
        (env2.FStarC_TypeChecker_Env.expected_typ);
      FStarC_TypeChecker_Env.sigtab = (env2.FStarC_TypeChecker_Env.sigtab);
      FStarC_TypeChecker_Env.attrtab = (env2.FStarC_TypeChecker_Env.attrtab);
      FStarC_TypeChecker_Env.instantiate_imp =
        (env2.FStarC_TypeChecker_Env.instantiate_imp);
      FStarC_TypeChecker_Env.effects = (env2.FStarC_TypeChecker_Env.effects);
      FStarC_TypeChecker_Env.generalize =
        (env2.FStarC_TypeChecker_Env.generalize);
      FStarC_TypeChecker_Env.letrecs = (env2.FStarC_TypeChecker_Env.letrecs);
      FStarC_TypeChecker_Env.top_level =
        (env2.FStarC_TypeChecker_Env.top_level);
      FStarC_TypeChecker_Env.check_uvars =
        (env2.FStarC_TypeChecker_Env.check_uvars);
      FStarC_TypeChecker_Env.use_eq_strict =
        (env2.FStarC_TypeChecker_Env.use_eq_strict);
      FStarC_TypeChecker_Env.is_iface =
        (env2.FStarC_TypeChecker_Env.is_iface);
      FStarC_TypeChecker_Env.admit = (env2.FStarC_TypeChecker_Env.admit);
      FStarC_TypeChecker_Env.phase1 = (env2.FStarC_TypeChecker_Env.phase1);
      FStarC_TypeChecker_Env.failhard =
        (env2.FStarC_TypeChecker_Env.failhard);
      FStarC_TypeChecker_Env.flychecking =
        (env2.FStarC_TypeChecker_Env.flychecking);
      FStarC_TypeChecker_Env.uvar_subtyping =
        (env2.FStarC_TypeChecker_Env.uvar_subtyping);
      FStarC_TypeChecker_Env.intactics =
        (env2.FStarC_TypeChecker_Env.intactics);
      FStarC_TypeChecker_Env.nocoerce =
        (env2.FStarC_TypeChecker_Env.nocoerce);
      FStarC_TypeChecker_Env.tc_term = (env2.FStarC_TypeChecker_Env.tc_term);
      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
        (env2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
      FStarC_TypeChecker_Env.universe_of =
        (env2.FStarC_TypeChecker_Env.universe_of);
      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
        (env2.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
      FStarC_TypeChecker_Env.teq_nosmt_force =
        (env2.FStarC_TypeChecker_Env.teq_nosmt_force);
      FStarC_TypeChecker_Env.subtype_nosmt_force =
        (env2.FStarC_TypeChecker_Env.subtype_nosmt_force);
      FStarC_TypeChecker_Env.qtbl_name_and_index =
        (env2.FStarC_TypeChecker_Env.qtbl_name_and_index);
      FStarC_TypeChecker_Env.normalized_eff_names =
        (env2.FStarC_TypeChecker_Env.normalized_eff_names);
      FStarC_TypeChecker_Env.fv_delta_depths =
        (env2.FStarC_TypeChecker_Env.fv_delta_depths);
      FStarC_TypeChecker_Env.proof_ns =
        (env2.FStarC_TypeChecker_Env.proof_ns);
      FStarC_TypeChecker_Env.synth_hook =
        (env2.FStarC_TypeChecker_Env.synth_hook);
      FStarC_TypeChecker_Env.try_solve_implicits_hook =
        (env2.FStarC_TypeChecker_Env.try_solve_implicits_hook);
      FStarC_TypeChecker_Env.splice = FStarC_Tactics_Hooks.splice;
      FStarC_TypeChecker_Env.mpreprocess =
        (env2.FStarC_TypeChecker_Env.mpreprocess);
      FStarC_TypeChecker_Env.postprocess =
        (env2.FStarC_TypeChecker_Env.postprocess);
      FStarC_TypeChecker_Env.identifier_info =
        (env2.FStarC_TypeChecker_Env.identifier_info);
      FStarC_TypeChecker_Env.tc_hooks =
        (env2.FStarC_TypeChecker_Env.tc_hooks);
      FStarC_TypeChecker_Env.dsenv = (env2.FStarC_TypeChecker_Env.dsenv);
      FStarC_TypeChecker_Env.nbe = (env2.FStarC_TypeChecker_Env.nbe);
      FStarC_TypeChecker_Env.strict_args_tab =
        (env2.FStarC_TypeChecker_Env.strict_args_tab);
      FStarC_TypeChecker_Env.erasable_types_tab =
        (env2.FStarC_TypeChecker_Env.erasable_types_tab);
      FStarC_TypeChecker_Env.enable_defer_to_tac =
        (env2.FStarC_TypeChecker_Env.enable_defer_to_tac);
      FStarC_TypeChecker_Env.unif_allow_ref_guards =
        (env2.FStarC_TypeChecker_Env.unif_allow_ref_guards);
      FStarC_TypeChecker_Env.erase_erasable_args =
        (env2.FStarC_TypeChecker_Env.erase_erasable_args);
      FStarC_TypeChecker_Env.core_check =
        (env2.FStarC_TypeChecker_Env.core_check);
      FStarC_TypeChecker_Env.missing_decl =
        (env2.FStarC_TypeChecker_Env.missing_decl)
    } in
  let env4 =
    {
      FStarC_TypeChecker_Env.solver = (env3.FStarC_TypeChecker_Env.solver);
      FStarC_TypeChecker_Env.range = (env3.FStarC_TypeChecker_Env.range);
      FStarC_TypeChecker_Env.curmodule =
        (env3.FStarC_TypeChecker_Env.curmodule);
      FStarC_TypeChecker_Env.gamma = (env3.FStarC_TypeChecker_Env.gamma);
      FStarC_TypeChecker_Env.gamma_sig =
        (env3.FStarC_TypeChecker_Env.gamma_sig);
      FStarC_TypeChecker_Env.gamma_cache =
        (env3.FStarC_TypeChecker_Env.gamma_cache);
      FStarC_TypeChecker_Env.modules = (env3.FStarC_TypeChecker_Env.modules);
      FStarC_TypeChecker_Env.expected_typ =
        (env3.FStarC_TypeChecker_Env.expected_typ);
      FStarC_TypeChecker_Env.sigtab = (env3.FStarC_TypeChecker_Env.sigtab);
      FStarC_TypeChecker_Env.attrtab = (env3.FStarC_TypeChecker_Env.attrtab);
      FStarC_TypeChecker_Env.instantiate_imp =
        (env3.FStarC_TypeChecker_Env.instantiate_imp);
      FStarC_TypeChecker_Env.effects = (env3.FStarC_TypeChecker_Env.effects);
      FStarC_TypeChecker_Env.generalize =
        (env3.FStarC_TypeChecker_Env.generalize);
      FStarC_TypeChecker_Env.letrecs = (env3.FStarC_TypeChecker_Env.letrecs);
      FStarC_TypeChecker_Env.top_level =
        (env3.FStarC_TypeChecker_Env.top_level);
      FStarC_TypeChecker_Env.check_uvars =
        (env3.FStarC_TypeChecker_Env.check_uvars);
      FStarC_TypeChecker_Env.use_eq_strict =
        (env3.FStarC_TypeChecker_Env.use_eq_strict);
      FStarC_TypeChecker_Env.is_iface =
        (env3.FStarC_TypeChecker_Env.is_iface);
      FStarC_TypeChecker_Env.admit = (env3.FStarC_TypeChecker_Env.admit);
      FStarC_TypeChecker_Env.phase1 = (env3.FStarC_TypeChecker_Env.phase1);
      FStarC_TypeChecker_Env.failhard =
        (env3.FStarC_TypeChecker_Env.failhard);
      FStarC_TypeChecker_Env.flychecking =
        (env3.FStarC_TypeChecker_Env.flychecking);
      FStarC_TypeChecker_Env.uvar_subtyping =
        (env3.FStarC_TypeChecker_Env.uvar_subtyping);
      FStarC_TypeChecker_Env.intactics =
        (env3.FStarC_TypeChecker_Env.intactics);
      FStarC_TypeChecker_Env.nocoerce =
        (env3.FStarC_TypeChecker_Env.nocoerce);
      FStarC_TypeChecker_Env.tc_term = (env3.FStarC_TypeChecker_Env.tc_term);
      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
        (env3.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
      FStarC_TypeChecker_Env.universe_of =
        (env3.FStarC_TypeChecker_Env.universe_of);
      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
        (env3.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
      FStarC_TypeChecker_Env.teq_nosmt_force =
        (env3.FStarC_TypeChecker_Env.teq_nosmt_force);
      FStarC_TypeChecker_Env.subtype_nosmt_force =
        (env3.FStarC_TypeChecker_Env.subtype_nosmt_force);
      FStarC_TypeChecker_Env.qtbl_name_and_index =
        (env3.FStarC_TypeChecker_Env.qtbl_name_and_index);
      FStarC_TypeChecker_Env.normalized_eff_names =
        (env3.FStarC_TypeChecker_Env.normalized_eff_names);
      FStarC_TypeChecker_Env.fv_delta_depths =
        (env3.FStarC_TypeChecker_Env.fv_delta_depths);
      FStarC_TypeChecker_Env.proof_ns =
        (env3.FStarC_TypeChecker_Env.proof_ns);
      FStarC_TypeChecker_Env.synth_hook =
        (env3.FStarC_TypeChecker_Env.synth_hook);
      FStarC_TypeChecker_Env.try_solve_implicits_hook =
        (env3.FStarC_TypeChecker_Env.try_solve_implicits_hook);
      FStarC_TypeChecker_Env.splice = (env3.FStarC_TypeChecker_Env.splice);
      FStarC_TypeChecker_Env.mpreprocess = FStarC_Tactics_Hooks.mpreprocess;
      FStarC_TypeChecker_Env.postprocess =
        (env3.FStarC_TypeChecker_Env.postprocess);
      FStarC_TypeChecker_Env.identifier_info =
        (env3.FStarC_TypeChecker_Env.identifier_info);
      FStarC_TypeChecker_Env.tc_hooks =
        (env3.FStarC_TypeChecker_Env.tc_hooks);
      FStarC_TypeChecker_Env.dsenv = (env3.FStarC_TypeChecker_Env.dsenv);
      FStarC_TypeChecker_Env.nbe = (env3.FStarC_TypeChecker_Env.nbe);
      FStarC_TypeChecker_Env.strict_args_tab =
        (env3.FStarC_TypeChecker_Env.strict_args_tab);
      FStarC_TypeChecker_Env.erasable_types_tab =
        (env3.FStarC_TypeChecker_Env.erasable_types_tab);
      FStarC_TypeChecker_Env.enable_defer_to_tac =
        (env3.FStarC_TypeChecker_Env.enable_defer_to_tac);
      FStarC_TypeChecker_Env.unif_allow_ref_guards =
        (env3.FStarC_TypeChecker_Env.unif_allow_ref_guards);
      FStarC_TypeChecker_Env.erase_erasable_args =
        (env3.FStarC_TypeChecker_Env.erase_erasable_args);
      FStarC_TypeChecker_Env.core_check =
        (env3.FStarC_TypeChecker_Env.core_check);
      FStarC_TypeChecker_Env.missing_decl =
        (env3.FStarC_TypeChecker_Env.missing_decl)
    } in
  let env5 =
    {
      FStarC_TypeChecker_Env.solver = (env4.FStarC_TypeChecker_Env.solver);
      FStarC_TypeChecker_Env.range = (env4.FStarC_TypeChecker_Env.range);
      FStarC_TypeChecker_Env.curmodule =
        (env4.FStarC_TypeChecker_Env.curmodule);
      FStarC_TypeChecker_Env.gamma = (env4.FStarC_TypeChecker_Env.gamma);
      FStarC_TypeChecker_Env.gamma_sig =
        (env4.FStarC_TypeChecker_Env.gamma_sig);
      FStarC_TypeChecker_Env.gamma_cache =
        (env4.FStarC_TypeChecker_Env.gamma_cache);
      FStarC_TypeChecker_Env.modules = (env4.FStarC_TypeChecker_Env.modules);
      FStarC_TypeChecker_Env.expected_typ =
        (env4.FStarC_TypeChecker_Env.expected_typ);
      FStarC_TypeChecker_Env.sigtab = (env4.FStarC_TypeChecker_Env.sigtab);
      FStarC_TypeChecker_Env.attrtab = (env4.FStarC_TypeChecker_Env.attrtab);
      FStarC_TypeChecker_Env.instantiate_imp =
        (env4.FStarC_TypeChecker_Env.instantiate_imp);
      FStarC_TypeChecker_Env.effects = (env4.FStarC_TypeChecker_Env.effects);
      FStarC_TypeChecker_Env.generalize =
        (env4.FStarC_TypeChecker_Env.generalize);
      FStarC_TypeChecker_Env.letrecs = (env4.FStarC_TypeChecker_Env.letrecs);
      FStarC_TypeChecker_Env.top_level =
        (env4.FStarC_TypeChecker_Env.top_level);
      FStarC_TypeChecker_Env.check_uvars =
        (env4.FStarC_TypeChecker_Env.check_uvars);
      FStarC_TypeChecker_Env.use_eq_strict =
        (env4.FStarC_TypeChecker_Env.use_eq_strict);
      FStarC_TypeChecker_Env.is_iface =
        (env4.FStarC_TypeChecker_Env.is_iface);
      FStarC_TypeChecker_Env.admit = (env4.FStarC_TypeChecker_Env.admit);
      FStarC_TypeChecker_Env.phase1 = (env4.FStarC_TypeChecker_Env.phase1);
      FStarC_TypeChecker_Env.failhard =
        (env4.FStarC_TypeChecker_Env.failhard);
      FStarC_TypeChecker_Env.flychecking =
        (env4.FStarC_TypeChecker_Env.flychecking);
      FStarC_TypeChecker_Env.uvar_subtyping =
        (env4.FStarC_TypeChecker_Env.uvar_subtyping);
      FStarC_TypeChecker_Env.intactics =
        (env4.FStarC_TypeChecker_Env.intactics);
      FStarC_TypeChecker_Env.nocoerce =
        (env4.FStarC_TypeChecker_Env.nocoerce);
      FStarC_TypeChecker_Env.tc_term = (env4.FStarC_TypeChecker_Env.tc_term);
      FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
        (env4.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
      FStarC_TypeChecker_Env.universe_of =
        (env4.FStarC_TypeChecker_Env.universe_of);
      FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
        (env4.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
      FStarC_TypeChecker_Env.teq_nosmt_force =
        (env4.FStarC_TypeChecker_Env.teq_nosmt_force);
      FStarC_TypeChecker_Env.subtype_nosmt_force =
        (env4.FStarC_TypeChecker_Env.subtype_nosmt_force);
      FStarC_TypeChecker_Env.qtbl_name_and_index =
        (env4.FStarC_TypeChecker_Env.qtbl_name_and_index);
      FStarC_TypeChecker_Env.normalized_eff_names =
        (env4.FStarC_TypeChecker_Env.normalized_eff_names);
      FStarC_TypeChecker_Env.fv_delta_depths =
        (env4.FStarC_TypeChecker_Env.fv_delta_depths);
      FStarC_TypeChecker_Env.proof_ns =
        (env4.FStarC_TypeChecker_Env.proof_ns);
      FStarC_TypeChecker_Env.synth_hook =
        (env4.FStarC_TypeChecker_Env.synth_hook);
      FStarC_TypeChecker_Env.try_solve_implicits_hook =
        (env4.FStarC_TypeChecker_Env.try_solve_implicits_hook);
      FStarC_TypeChecker_Env.splice = (env4.FStarC_TypeChecker_Env.splice);
      FStarC_TypeChecker_Env.mpreprocess =
        (env4.FStarC_TypeChecker_Env.mpreprocess);
      FStarC_TypeChecker_Env.postprocess = FStarC_Tactics_Hooks.postprocess;
      FStarC_TypeChecker_Env.identifier_info =
        (env4.FStarC_TypeChecker_Env.identifier_info);
      FStarC_TypeChecker_Env.tc_hooks =
        (env4.FStarC_TypeChecker_Env.tc_hooks);
      FStarC_TypeChecker_Env.dsenv = (env4.FStarC_TypeChecker_Env.dsenv);
      FStarC_TypeChecker_Env.nbe = (env4.FStarC_TypeChecker_Env.nbe);
      FStarC_TypeChecker_Env.strict_args_tab =
        (env4.FStarC_TypeChecker_Env.strict_args_tab);
      FStarC_TypeChecker_Env.erasable_types_tab =
        (env4.FStarC_TypeChecker_Env.erasable_types_tab);
      FStarC_TypeChecker_Env.enable_defer_to_tac =
        (env4.FStarC_TypeChecker_Env.enable_defer_to_tac);
      FStarC_TypeChecker_Env.unif_allow_ref_guards =
        (env4.FStarC_TypeChecker_Env.unif_allow_ref_guards);
      FStarC_TypeChecker_Env.erase_erasable_args =
        (env4.FStarC_TypeChecker_Env.erase_erasable_args);
      FStarC_TypeChecker_Env.core_check =
        (env4.FStarC_TypeChecker_Env.core_check);
      FStarC_TypeChecker_Env.missing_decl =
        (env4.FStarC_TypeChecker_Env.missing_decl)
    } in
  (env5.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.init env5; env5
let batch_mode_tc (fly_deps : Prims.bool)
  (filenames : Prims.string Prims.list) (dep_graph : FStarC_Parser_Dep.deps)
  : (FStarC_CheckedFiles.tc_result Prims.list * uenv * (uenv -> uenv))=
  (let uu___1 = FStarC_Effect.op_Bang dbg_dep in
   if uu___1
   then
     (FStarC_Format.print_string "Auto-deps kicked in; here's some info.\n";
      FStarC_Format.print1
        "Here's the list of filenames we will process: %s\n"
        (FStarC_String.concat " " filenames);
      (let uu___4 =
         let uu___5 =
           FStarC_List.filter FStarC_Options.should_verify_file filenames in
         FStarC_String.concat " " uu___5 in
       FStarC_Format.print1 "Here's the list of modules we will verify: %s\n"
         uu___4))
   else ());
  (let env =
     let uu___1 = init_env dep_graph in
     FStarC_Extraction_ML_UEnv.new_uenv uu___1 in
   let uu___1 = tc_fold_interleave fly_deps ([], [], env) filenames in
   match uu___1 with
   | (all_mods, mllibs, env1) ->
       ((let uu___3 =
           let uu___4 = FStarC_Errors.get_err_count () in
           uu___4 = Prims.int_zero in
         if uu___3 then emit dep_graph mllibs else ());
        (let solver_refresh env2 =
           let uu___3 =
             with_tcenv_of_env env2
               (fun tcenv ->
                  (tcenv.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.finish
                    ();
                  ((), tcenv)) in
           FStar_Pervasives_Native.snd uu___3 in
         (all_mods, env1, solver_refresh))))
