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
          FStarC_TypeChecker_Env.expected_post =
            (tcenv.FStarC_TypeChecker_Env.expected_post);
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
            (tcenv.FStarC_TypeChecker_Env.missing_decl);
          FStarC_TypeChecker_Env.iface_todo =
            (tcenv.FStarC_TypeChecker_Env.iface_todo);
          FStarC_TypeChecker_Env.iface_hidden =
            (tcenv.FStarC_TypeChecker_Env.iface_hidden);
          FStarC_TypeChecker_Env.iface_lids =
            (tcenv.FStarC_TypeChecker_Env.iface_lids);
          FStarC_TypeChecker_Env.iface_val_lids =
            (tcenv.FStarC_TypeChecker_Env.iface_val_lids)
        })
let with_tcenv_of_env (e : uenv)
  (f : FStarC_TypeChecker_Env.env -> ('a * FStarC_TypeChecker_Env.env)) :
  ('a * uenv)=
  let uu___ = f (FStarC_Extraction_ML_UEnv.tcenv_of_uenv e) in
  match uu___ with
  | (a1, t') -> (a1, (FStarC_Extraction_ML_UEnv.set_tcenv e t'))
let with_dsenv_of_env (e : uenv) (f : 'a FStarC_Syntax_DsEnv.withenv) :
  ('a * uenv)=
  let uu___ =
    with_dsenv_of_tcenv (FStarC_Extraction_ML_UEnv.tcenv_of_uenv e) f in
  match uu___ with
  | (a1, tcenv) -> (a1, (FStarC_Extraction_ML_UEnv.set_tcenv e tcenv))
let push_env (env : uenv) : uenv=
  let uu___ =
    with_tcenv_of_env env
      (fun tcenv ->
         let uu___1 =
           FStarC_TypeChecker_Env.push
             (FStarC_Extraction_ML_UEnv.tcenv_of_uenv env)
             "top-level: push_env" in
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
let iface_solver_frames :
  (FStarC_TypeChecker_Env.solver_depth_t * (FStarC_Syntax_Syntax.modul *
    FStarC_SMTEncoding_Env.module_encoding) Prims.list) Prims.list
    FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let record_encoded_modul (m : FStarC_Syntax_Syntax.modul)
  (smt_decls : FStarC_SMTEncoding_Env.module_encoding) : unit=
  let uu___ =
    let uu___1 = FStarC_Effect.op_Bang iface_solver_frames in
    FStarC_List.map
      (fun uu___2 ->
         match uu___2 with
         | (depth, pending) -> (depth, ((m, smt_decls) :: pending))) uu___1 in
  FStarC_Effect.op_Colon_Equals iface_solver_frames uu___
let push_iface_solver_frame (env : uenv) (name : Prims.string) : unit=
  let tcenv = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env in
  let uu___ =
    (tcenv.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.snapshot
      name in
  match uu___ with
  | (depth, ()) ->
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang iface_solver_frames in (depth, [])
          :: uu___2 in
      FStarC_Effect.op_Colon_Equals iface_solver_frames uu___1
let pop_iface_solver_frame (env : uenv) (name : Prims.string) : unit=
  let uu___ = FStarC_Effect.op_Bang iface_solver_frames in
  match uu___ with
  | [] -> ()
  | (depth, pending)::rest ->
      (FStarC_Effect.op_Colon_Equals iface_solver_frames rest;
       (let tcenv = FStarC_Extraction_ML_UEnv.tcenv_of_uenv env in
        (tcenv.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.rollback
          name (FStar_Pervasives_Native.Some depth);
        (let uu___4 =
           let uu___5 = FStarC_Options.interactive () in Prims.not uu___5 in
         if uu___4
         then
           FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.reset_scope
             ()
         else ());
        FStarC_List.iter
          (fun uu___4 ->
             match uu___4 with
             | (tcmod, smt_decls) ->
                 (if
                    Prims.not
                      (FStarC_SMTEncoding_Env.is_empty_encoding smt_decls)
                  then
                    FStarC_SMTEncoding_Encode.encode_modul_from_cache tcenv
                      tcmod smt_decls
                  else ();
                  record_encoded_modul tcmod smt_decls))
          (FStarC_List.rev pending)))
let is_iface_of (fn : Prims.string)
  (root : Prims.string FStar_Pervasives_Native.option) : Prims.bool=
  let uu___ = FStarC_Parser_Dep.is_interface fn in
  if uu___
  then
    match root with
    | FStar_Pervasives_Native.Some r ->
        let uu___1 = FStarC_Parser_Dep.is_implementation r in
        (if uu___1
         then
           let uu___2 = FStarC_Parser_Dep.module_name_of_file r in
           let uu___3 = FStarC_Parser_Dep.module_name_of_file fn in
           uu___2 = uu___3
         else false)
    | FStar_Pervasives_Native.None -> false
  else false
let env_of_tcenv (env : FStarC_TypeChecker_Env.env) :
  FStarC_Extraction_ML_UEnv.uenv= FStarC_Extraction_ML_UEnv.new_uenv env
let parse (fly_deps : Prims.bool) (env : uenv) (fn : Prims.string) :
  (FStarC_Ident.lident * (FStarC_Parser_AST.modul,
    FStarC_Syntax_Syntax.modul) FStar_Pervasives.either * uenv)=
  let uu___ = FStarC_Parser_Driver.parse_file fn in
  match uu___ with
  | (ast, uu___1) ->
      if fly_deps
      then
        ((FStarC_Parser_AST.lid_of_modul ast), (FStar_Pervasives.Inl ast),
          env)
      else
        (let uu___2 =
           let uu___3 = FStarC_ToSyntax_ToSyntax.ast_modul_to_modul ast in
           with_dsenv_of_env env uu___3 in
         match uu___2 with
         | (mod1, env1) ->
             ((FStarC_Parser_AST.lid_of_modul ast),
               (FStar_Pervasives.Inr mod1), env1))
let core_check : FStarC_TypeChecker_Env.core_check_t=
  fun env tm t must_tot ->
    let uu___ =
      let uu___1 = FStarC_Options.compat_pre_core_should_check () in
      Prims.not uu___1 in
    if uu___
    then FStar_Pervasives.Inl FStar_Pervasives_Native.None
    else
      (let uu___1 = FStarC_TypeChecker_Core.check_term env tm t must_tot in
       match uu___1 with
       | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
           FStar_Pervasives.Inl FStar_Pervasives_Native.None
       | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
           let uu___2 = FStarC_Options.compat_pre_core_set () in
           if uu___2
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
      (fun d ->
         match d.FStarC_Parser_AST.d with
         | FStarC_Parser_AST.UseLangDecls _0 -> true
         | uu___ -> false) ds in
  let uu___ = use_lang_decl lang_decls in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      FStarC_Parser_Driver.parse_fragment FStar_Pervasives_Native.None frag
  | FStar_Pervasives_Native.Some
      { FStarC_Parser_AST.d = FStarC_Parser_AST.UseLangDecls lang;
        FStarC_Parser_AST.drange = uu___1; FStarC_Parser_AST.quals = uu___2;
        FStarC_Parser_AST.attrs = uu___3;_}
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
    uu___ =
      (FStarC_String.lowercase
         (FStarC_Ident.string_of_lid
            (FStarC_Parser_AST.lid_of_modul ast_modul))) in
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
    (let uu___1 =
       let uu___2 = acceptable_mod_name ast_modul in Prims.not uu___2 in
     if uu___1
     then
       let msg =
         let uu___2 =
           let uu___3 = fname env in
           FStarC_Parser_Dep.module_name_of_file uu___3 in
         FStarC_Format.fmt1
           "Interactive mode only supports a single module at the top-level. Expected module %s"
           uu___2 in
       FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
         (range_of_first_mod_decl ast_modul)
         FStarC_Errors_Codes.Fatal_NonSingletonTopLevelModule ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic msg)
     else ());
    (let uu___1 =
       if FStarC_Syntax_DsEnv.syntax_only env.FStarC_TypeChecker_Env.dsenv
       then
         let uu___2 =
           FStarC_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod
             ast_modul in
         with_dsenv_of_tcenv env uu___2
       else
         (let uu___2 =
            let uu___3 =
              FStarC_ToSyntax_ToSyntax.partial_ast_modul_to_modul curmod
                ast_modul in
            with_dsenv_of_tcenv env uu___3 in
          match uu___2 with
          | (m, env1) -> FStarC_TypeChecker_Tc.tc_partial_modul env1 m) in
     match uu___1 with
     | (modul, env1) ->
         let lang_decls =
           let decls =
             match ast_modul with
             | FStarC_Parser_AST.Module
                 { FStarC_Parser_AST.no_prelude = uu___2;
                   FStarC_Parser_AST.mname = uu___3;
                   FStarC_Parser_AST.decls = decls1;_}
                 -> decls1
             | FStarC_Parser_AST.Interface
                 { FStarC_Parser_AST.no_prelude1 = uu___2;
                   FStarC_Parser_AST.mname1 = uu___3;
                   FStarC_Parser_AST.decls1 = decls1;
                   FStarC_Parser_AST.admitted = uu___4;_}
                 -> decls1 in
           FStarC_List.filter filter_lang_decls decls in
         ((FStar_Pervasives_Native.Some modul), env1, lang_decls)) in
  let check_decls ast_decls =
    match curmod with
    | FStar_Pervasives_Native.None ->
        let uu___ = FStarC_List.hd ast_decls in
        (match uu___ with
         | { FStarC_Parser_AST.d = uu___1; FStarC_Parser_AST.drange = rng;
             FStarC_Parser_AST.quals = uu___2;
             FStarC_Parser_AST.attrs = uu___3;_} ->
             FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
               rng FStarC_Errors_Codes.Fatal_ModuleFirstStatement ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic "First statement must be a module declaration"))
    | FStar_Pervasives_Native.Some modul ->
        let uu___ =
          if FStarC_Syntax_DsEnv.syntax_only env.FStarC_TypeChecker_Env.dsenv
          then
            let uu___1 =
              let uu___2 =
                FStarC_ToSyntax_ToSyntax.decls_to_sigelts ast_decls in
              with_dsenv_of_tcenv env uu___2 in
            match uu___1 with | (uu___2, env1) -> (modul, [], env1)
          else
            (let uu___1 =
               let uu___2 =
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Ident.showable_lident
                     modul.FStarC_Syntax_Syntax.name in
                 Prims.strcat "While desugaring module " uu___3 in
               FStarC_Errors.with_ctx uu___2
                 (fun uu___3 ->
                    let uu___4 =
                      FStarC_ToSyntax_ToSyntax.decls_to_sigelts ast_decls in
                    with_dsenv_of_tcenv env uu___4) in
             match uu___1 with
             | (ses, env1) ->
                 FStarC_TypeChecker_Tc.tc_more_partial_modul env1 modul ses) in
        (match uu___ with
         | (modul1, uu___1, env1) ->
             let uu___2 = FStarC_List.filter filter_lang_decls ast_decls in
             ((FStar_Pervasives_Native.Some modul1), env1, uu___2)) in
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
              let uu___1 = FStarC_Options.no_prelude () in
              if uu___1
              then true
              else
                FStarC_List.existsb
                  (fun uu___2 ->
                     match uu___2.FStarC_Parser_AST.tm with
                     | FStarC_Parser_AST.Const (FStarC_Const.Const_string
                         ("no_prelude", uu___3)) -> true
                     | uu___3 -> false) d.FStarC_Parser_AST.attrs in
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
    FStarC_Effect.failwith uu___1 in
  if opt <> FStar_Pervasives_Native.None
  then
    let ext =
      match opt with
      | FStar_Pervasives_Native.Some (FStarC_Options.FSharp) -> ".fs"
      | FStar_Pervasives_Native.Some (FStarC_Options.OCaml) -> ".ml"
      | FStar_Pervasives_Native.Some (FStarC_Options.Plugin) -> ".ml"
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
            let uu___2 =
              let uu___3 = FStarC_Options.output_to () in
              match uu___3 with
              | FStar_Pervasives_Native.Some v -> true
              | uu___4 -> false in
            if uu___2
            then (FStarC_List.length mllib) > Prims.int_one
            else false in
          if uu___1
          then
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic
                 [FStarC_Errors_Msg.text
                    "Cannot provide -o and extract multiple modules";
                 FStarC_Errors_Msg.text
                   "Please use -o with a single module, or specify an output directory with --odir"])
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
                           Prims.strcat
                             (FStarC_Extraction_ML_Util.flatten_mlpath p) ext in
                         ofile basename in
                       let ml = printer mlmodule in
                       FStarC_Util.write_file filename ml)) mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.OCaml) ->
        let printer =
          if opt = (FStar_Pervasives_Native.Some FStarC_Options.FSharp)
          then FStarC_Extraction_ML_PrintFS.print_fs
          else FStarC_Extraction_ML_PrintML.print_ml in
        ((let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Options.output_to () in
              match uu___3 with
              | FStar_Pervasives_Native.Some v -> true
              | uu___4 -> false in
            if uu___2
            then (FStarC_List.length mllib) > Prims.int_one
            else false in
          if uu___1
          then
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic
                 [FStarC_Errors_Msg.text
                    "Cannot provide -o and extract multiple modules";
                 FStarC_Errors_Msg.text
                   "Please use -o with a single module, or specify an output directory with --odir"])
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
                           Prims.strcat
                             (FStarC_Extraction_ML_Util.flatten_mlpath p) ext in
                         ofile basename in
                       let ml = printer mlmodule in
                       FStarC_Util.write_file filename ml)) mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.Plugin) ->
        let printer =
          if opt = (FStar_Pervasives_Native.Some FStarC_Options.FSharp)
          then FStarC_Extraction_ML_PrintFS.print_fs
          else FStarC_Extraction_ML_PrintML.print_ml in
        ((let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Options.output_to () in
              match uu___3 with
              | FStar_Pervasives_Native.Some v -> true
              | uu___4 -> false in
            if uu___2
            then (FStarC_List.length mllib) > Prims.int_one
            else false in
          if uu___1
          then
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic
                 [FStarC_Errors_Msg.text
                    "Cannot provide -o and extract multiple modules";
                 FStarC_Errors_Msg.text
                   "Please use -o with a single module, or specify an output directory with --odir"])
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
                           Prims.strcat
                             (FStarC_Extraction_ML_Util.flatten_mlpath p) ext in
                         ofile basename in
                       let ml = printer mlmodule in
                       FStarC_Util.write_file filename ml)) mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.Extension) ->
        ((let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Options.output_to () in
              match uu___3 with
              | FStar_Pervasives_Native.Some v -> true
              | uu___4 -> false in
            if uu___2
            then (FStarC_List.length mllib) > Prims.int_one
            else false in
          if uu___1
          then
            FStarC_Errors.raise_error0
              FStarC_Errors_Codes.Fatal_OptionsNotCompatible ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic
                 [FStarC_Errors_Msg.text
                    "Cannot provide -o and extract multiple modules";
                 FStarC_Errors_Msg.text
                   "Please use -o with a single module, or specify an output directory with --odir"])
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
                           Prims.strcat
                             (FStarC_Extraction_ML_Util.flatten_mlpath mname)
                             ext in
                         ofile basename in
                       (match modul with
                        | FStar_Pervasives_Native.Some (uu___3, decls) ->
                            let bindings =
                              FStarC_Extraction_ML_UEnv.bindings_of_uenv env in
                            let deps =
                              FStarC_Parser_Dep.deps_of_modul dep_graph
                                (FStarC_Extraction_ML_Syntax.string_of_mlpath
                                   mname) in
                            FStarC_Util.save_value_to_file filename
                              (deps, bindings, decls)
                        | FStar_Pervasives_Native.None ->
                            FStarC_Effect.failwith
                              "Unexpected ml modul in Extension extraction mode")))
           mllib)
    | FStar_Pervasives_Native.Some (FStarC_Options.Krml) ->
        let programs =
          FStarC_List.collect
            (fun uu___ ->
               match uu___ with
               | (ue, m) -> FStarC_Extraction_Krml.translate ue [m]) mllib in
        let programs1 =
          let rec dedup seen ps =
            match ps with
            | [] -> []
            | (name, decls)::ps1 ->
                let uu___ = FStarC_List.existsb (fun n -> n = name) seen in
                if uu___
                then dedup seen ps1
                else
                  (let uu___1 = dedup (name :: seen) ps1 in (name, decls) ::
                     uu___1) in
          let uu___ = dedup [] (FStarC_List.rev programs) in
          FStarC_List.rev uu___ in
        let bin = (FStarC_Extraction_Krml.current_version, programs1) in
        let oname =
          let uu___ = FStarC_Options.krmloutput () in
          match uu___ with
          | FStar_Pervasives_Native.Some fname -> fname
          | uu___1 ->
              (match programs1 with
               | (name, uu___2)::[] ->
                   FStarC_Find.prepend_output_dir (Prims.strcat name ext)
               | uu___2 ->
                   FStarC_Find.prepend_output_dir (Prims.strcat "out" ext)) in
        FStarC_Util.save_value_to_file oname bin
    | uu___ -> fail ()
  else ()
let rec tc_one_file_internal (fly_deps : Prims.bool)
  (skip_solver : Prims.bool) (env : uenv) (fn : Prims.string) :
  (FStarC_CheckedFiles.tc_result * FStarC_Extraction_ML_Syntax.mlmodule
    FStar_Pervasives_Native.option * uenv)=
  if skip_solver
  then
    let name =
      let uu___ = FStarC_Parser_Dep.module_name_of_file fn in
      Prims.strcat "interface of " uu___ in
    (push_iface_solver_frame env name;
     (let res = tc_one_file_no_frame fly_deps true env fn in
      pop_iface_solver_frame env name; res))
  else tc_one_file_no_frame fly_deps false env fn
and tc_one_file_no_frame (fly_deps : Prims.bool) (skip_solver : Prims.bool)
  (env : uenv) (fn : Prims.string) :
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
                  FStarC_Options.should_extract
                    (FStarC_Ident.string_of_lid
                       tcmod.FStarC_Syntax_Syntax.name) tgt in
                Prims.not uu___4 in
              if uu___3
              then (FStar_Pervasives_Native.None, Prims.int_zero)
              else
                FStarC_Timing.record_ms
                  (fun uu___4 ->
                     with_env env1
                       (fun env2 ->
                          let uu___5 =
                            FStarC_Extraction_ML_Modul.extract env2 tcmod in
                          match uu___5 with | (uu___6, defs) -> defs)) in
        let maybe_extract_ml_iface tcmod env1 =
          let uu___2 =
            let uu___3 = FStarC_Options.codegen () in
            uu___3 = FStar_Pervasives_Native.None in
          if uu___2
          then (env1, Prims.int_zero)
          else
            FStarC_Timing.record_ms
              (fun uu___3 ->
                 let uu___4 =
                   with_env env1
                     (fun env2 ->
                        FStarC_Extraction_ML_Modul.extract_iface env2 tcmod) in
                 match uu___4 with | (env2, uu___5) -> env2) in
        let tc_source_file uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Parser_Dep.module_name_of_file fn in
              FStar_Pervasives_Native.Some uu___5 in
            FStarC_Profiling.profile (fun uu___5 -> parse fly_deps env fn)
              uu___4 "FStarC.Universal.tc_source_file.parse" in
          match uu___3 with
          | (mname, fmod, env1) ->
              let check_mod uu___4 =
                let check env2 =
                  FStarC_SMTEncoding_Z3.refresh FStar_Pervasives_Native.None;
                  (let uu___6 =
                     if fly_deps
                     then
                       let uu___7 = fmod in
                       match uu___7 with
                       | FStar_Pervasives.Inl ast_mod ->
                           fly_deps_check fn env2 ast_mod
                     else
                       (let uu___7 = fmod in
                        match uu___7 with
                        | FStar_Pervasives.Inr mod1 ->
                            with_tcenv_of_env env2
                              (fun tcenv ->
                                 FStarC_TypeChecker_Tc.check_module tcenv
                                   mod1)) in
                   match uu___6 with
                   | (modul, env3) ->
                       (restore_opts ();
                        (let smt_decls =
                           if skip_solver
                           then
                             FStarC_SMTEncoding_Encode.encode_modul_no_solver
                               (FStarC_Extraction_ML_UEnv.tcenv_of_uenv env3)
                               modul
                           else
                             FStarC_SMTEncoding_Encode.encode_modul
                               (FStarC_Extraction_ML_UEnv.tcenv_of_uenv env3)
                               modul in
                         if Prims.not skip_solver
                         then record_encoded_modul modul smt_decls
                         else ();
                         ((modul, smt_decls), env3)))) in
                let uu___5 =
                  FStarC_Profiling.profile (fun uu___6 -> check env1)
                    (FStar_Pervasives_Native.Some
                       (FStarC_Ident.string_of_lid mname))
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
                                  FStarC_TypeChecker_Env.dep_graph
                                    (FStarC_Extraction_ML_UEnv.tcenv_of_uenv
                                       env3) in
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
                                FStarC_Syntax_DsEnv.inclusion_info
                                  (FStarC_Extraction_ML_UEnv.tcenv_of_uenv
                                     env3).FStarC_TypeChecker_Env.dsenv mname in
                              (pd,
                                {
                                  FStarC_CheckedFiles.checked_module = tcmod;
                                  FStarC_CheckedFiles.mii = mii;
                                  FStarC_CheckedFiles.smt_encoding =
                                    smt_decls;
                                  FStarC_CheckedFiles.tc_time = tc_time;
                                  FStarC_CheckedFiles.extraction_time =
                                    (extract_time + iface_extraction_time)
                                }, extracted_defs, env3))) in
              check_mod () in
        let uu___2 =
          let uu___3 = FStarC_Options.cache_off () in Prims.not uu___3 in
        if uu___2
        then
          let r =
            let uu___3 =
              if fly_deps then FStarC_Options.should_check_file fn else false in
            if uu___3
            then FStar_Pervasives_Native.None
            else
              FStarC_CheckedFiles.load_module_from_cache
                (FStarC_Extraction_ML_UEnv.tcenv_of_uenv env) fn in
          let r1 =
            let uu___3 =
              let uu___4 = FStarC_Options.should_check_file fn in
              if uu___4
              then
                let uu___5 = FStarC_Options.force () in
                (if uu___5
                 then true
                 else
                   (let uu___6 =
                      let uu___7 = FStarC_Options.output_to () in
                      match uu___7 with
                      | FStar_Pervasives_Native.Some v -> true
                      | uu___8 -> false in
                    if uu___6
                    then
                      let uu___7 = FStarC_Options.codegen () in
                      match uu___7 with
                      | FStar_Pervasives_Native.None -> true
                      | uu___8 -> false
                    else false))
              else false in
            if uu___3 then FStar_Pervasives_Native.None else r in
          match r1 with
          | FStar_Pervasives_Native.None ->
              ((let uu___4 =
                  let uu___5 =
                    let uu___6 = FStarC_Parser_Dep.module_name_of_file fn in
                    FStarC_Options.should_be_already_cached uu___6 in
                  if uu___5
                  then
                    let uu___6 = FStarC_Options.force () in Prims.not uu___6
                  else false in
                if uu___4
                then
                  FStarC_Errors.raise_error0
                    FStarC_Errors_Codes.Error_AlreadyCachedAssertionFailure
                    ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic
                       [FStarC_Errors_Msg.text
                          (FStarC_Format.fmt1
                             "Expected %s to already be checked." fn)])
                else ());
               (let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = FStarC_Options.codegen () in
                      match uu___8 with
                      | FStar_Pervasives_Native.Some v -> true
                      | uu___9 -> false in
                    if uu___7 then FStarC_Options.cmi () else false in
                  if uu___6
                  then
                    let uu___7 = FStarC_Options.force () in Prims.not uu___7
                  else false in
                if uu___5
                then
                  FStarC_Errors.raise_error0
                    FStarC_Errors_Codes.Error_AlreadyCachedAssertionFailure
                    ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic
                       [FStarC_Errors_Msg.text
                          "Cross-module inlining expects all modules to be checked first.";
                       FStarC_Errors_Msg.text
                         (FStarC_Format.fmt1 "Module %s was not checked." fn)])
                else ());
               (let uu___5 = tc_source_file () in
                match uu___5 with
                | (parsing_data, tc_result, mllib, env1) ->
                    ((let uu___7 =
                        let uu___8 =
                          let uu___9 = FStarC_Errors.get_err_count () in
                          uu___9 = Prims.int_zero in
                        if uu___8
                        then FStarC_Options.should_write_checked_file fn
                        else false in
                      if uu___7
                      then
                        FStarC_CheckedFiles.store_module_to_cache
                          (FStarC_Extraction_ML_UEnv.tcenv_of_uenv env1) fn
                          parsing_data tc_result
                      else ());
                     (tc_result, mllib, env1))))
          | FStar_Pervasives_Native.Some tc_result ->
              let tcmod = tc_result.FStarC_CheckedFiles.checked_module in
              ((let uu___4 =
                  FStarC_Options.dump_module
                    (FStarC_Ident.string_of_lid
                       tcmod.FStarC_Syntax_Syntax.name) in
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
                       if Prims.not skip_solver
                       then
                         FStarC_SMTEncoding_Encode.defer_encoding
                           (fun uu___8 ->
                              let smt_decls =
                                tc_result.FStarC_CheckedFiles.smt_encoding in
                              if
                                Prims.not
                                  (FStarC_SMTEncoding_Env.is_empty_encoding
                                     smt_decls)
                              then
                                FStarC_SMTEncoding_Encode.encode_modul_from_cache
                                  env1 tcmod1 smt_decls
                              else ();
                              record_encoded_modul tcmod1 smt_decls)
                       else ();
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
                        let uu___6 =
                          FStarC_Options.should_extract
                            (FStarC_Ident.string_of_lid
                               tcmod.FStarC_Syntax_Syntax.name) tgt in
                        if uu___6
                        then
                          (Prims.not tcmod.FStarC_Syntax_Syntax.is_interface)
                            || (tgt = FStarC_Options.Krml)
                        else false in
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
          (let uu___3 = tc_source_file () in
           match uu___3 with
           | (uu___4, tc_result, mllib, env1) -> (tc_result, mllib, env1))))
and fly_deps_check (filename : Prims.string) (env : uenv)
  (ast_mod : FStarC_Parser_AST.modul) : (FStarC_Syntax_Syntax.modul * uenv)=
  let decls = FStarC_Parser_AST.decls_of_modul ast_mod in
  let mname =
    match decls with
    | { FStarC_Parser_AST.d = FStarC_Parser_AST.TopLevelModule lid;
        FStarC_Parser_AST.drange = uu___; FStarC_Parser_AST.quals = uu___1;
        FStarC_Parser_AST.attrs = uu___2;_}::rest -> lid
    | uu___ ->
        FStarC_Effect.failwith "Impossible: first decl is not a module" in
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
  FStarC_Parser_Dep.populate_parsing_data filename ast_mod
    (FStarC_Syntax_DsEnv.dep_graph
       (FStarC_Extraction_ML_UEnv.tcenv_of_uenv env).FStarC_TypeChecker_Env.dsenv);
  (let is_interface = FStarC_Parser_Dep.is_interface filename in
   let env1 =
     FStarC_List.fold_left
       (fun env2 d ->
          match d.FStarC_Parser_AST.d with
          | FStarC_Parser_AST.Friend uu___2 ->
              let uu___3 =
                scan_and_load_fly_deps_internal filename env2
                  (FStar_Pervasives.Inr d) in
              FStar_Pervasives_Native.fst uu___3
          | uu___2 -> env2) env decls in
   let uu___2 =
     FStarC_List.fold_left
       (fun uu___3 decl ->
          match uu___3 with
          | (mod1, env2) ->
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
                  scan_and_load_fly_deps_internal filename env2
                    (FStar_Pervasives.Inr decl) in
                match uu___5 with
                | (env3, uu___6) ->
                    let uu___7 =
                      with_tcenv_of_env env3
                        (fun tcenv ->
                           let uu___8 =
                             tc_one_fragment is_interface mod1 tcenv
                               (FStar_Pervasives.Inr decl) in
                           match uu___8 with
                           | (mod2, tcenv1, uu___9) -> (mod2, tcenv1)) in
                    (match uu___7 with | (mod2, env4) -> (mod2, env4)))))
       (FStar_Pervasives_Native.None, env1) decls in
   match uu___2 with
   | (mod1, env2) ->
       (if
          (match mod1 with
           | FStar_Pervasives_Native.None -> true
           | uu___4 -> false)
        then FStarC_Effect.failwith "Impossible"
        else ();
        (let uu___4 = mod1 in
         match uu___4 with
         | FStar_Pervasives_Native.Some mod2 ->
             let uu___5 =
               with_tcenv_of_env env2
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
                            FStarC_TypeChecker_Env.expected_post =
                              (tcenv.FStarC_TypeChecker_Env.expected_post);
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
                              (tcenv.FStarC_TypeChecker_Env.missing_decl);
                            FStarC_TypeChecker_Env.iface_todo =
                              (tcenv.FStarC_TypeChecker_Env.iface_todo);
                            FStarC_TypeChecker_Env.iface_hidden =
                              (tcenv.FStarC_TypeChecker_Env.iface_hidden);
                            FStarC_TypeChecker_Env.iface_lids =
                              (tcenv.FStarC_TypeChecker_Env.iface_lids);
                            FStarC_TypeChecker_Env.iface_val_lids =
                              (tcenv.FStarC_TypeChecker_Env.iface_val_lids)
                          } in
                        FStarC_TypeChecker_Tc.finish_partial_modul false
                          false tcenv1 mod3) in
             (match uu___5 with | (mod3, env3) -> (mod3, env3)))))
and scan_and_load_fly_deps_internal (filename : Prims.string) (env : uenv)
  (frag_or_decl :
    ((FStarC_Parser_ParseIt.input_frag * lang_decls_t),
      FStarC_Parser_AST.decl) FStar_Pervasives.either)
  : (uenv * Prims.string Prims.list)=
  let load_fly_deps env1 filenames =
    match filenames with
    | [] -> env1
    | uu___ ->
        let run_load_tasks env2 filenames1 =
          let uu___1 =
            tc_fold_interleave false (FStar_Pervasives_Native.Some filename)
              ([], [], env2) filenames1 in
          match uu___1 with | (uu___2, uu___3, env3) -> env3 in
        let uu___1 =
          FStarC_Extraction_ML_UEnv.with_restored_tc_scope env1
            (fun env2 ->
               let uu___2 = run_load_tasks env2 filenames in ((), uu___2)) in
        (match uu___1 with
         | (uu___2, env2) ->
             ((let uu___4 = FStarC_Parser_Dep.debug_fly_deps () in
               if uu___4
               then
                 let uu___5 =
                   FStarC_Class_Show.show FStarC_Syntax_DsEnv.showable_env
                     (FStarC_Extraction_ML_UEnv.tcenv_of_uenv env2).FStarC_TypeChecker_Env.dsenv in
                 FStarC_Format.print1 "After fly load deps: %s\n" uu___5
               else ());
              env2)) in
  let scan_fragment_deps env1 frag_or_decl1 =
    let deps =
      FStarC_Syntax_DsEnv.dep_graph env1.FStarC_TypeChecker_Env.dsenv in
    let deps1 = FStarC_Parser_Dep.copy_deps deps in
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
        FStarC_TypeChecker_Env.modules =
          (env1.FStarC_TypeChecker_Env.modules);
        FStarC_TypeChecker_Env.expected_typ =
          (env1.FStarC_TypeChecker_Env.expected_typ);
        FStarC_TypeChecker_Env.expected_post =
          (env1.FStarC_TypeChecker_Env.expected_post);
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
        FStarC_TypeChecker_Env.dsenv =
          (FStarC_Syntax_DsEnv.set_dep_graph
             env1.FStarC_TypeChecker_Env.dsenv deps1);
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
          (env1.FStarC_TypeChecker_Env.missing_decl);
        FStarC_TypeChecker_Env.iface_todo =
          (env1.FStarC_TypeChecker_Env.iface_todo);
        FStarC_TypeChecker_Env.iface_hidden =
          (env1.FStarC_TypeChecker_Env.iface_hidden);
        FStarC_TypeChecker_Env.iface_lids =
          (env1.FStarC_TypeChecker_Env.iface_lids);
        FStarC_TypeChecker_Env.iface_val_lids =
          (env1.FStarC_TypeChecker_Env.iface_val_lids)
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
     let already_loaded fn =
       let mname = FStarC_Parser_Dep.module_name_of_file fn in
       FStarC_List.filter
         (fun m ->
            mname = (FStarC_Ident.string_of_lid m.FStarC_Syntax_Syntax.name))
         env2.FStarC_TypeChecker_Env.modules in
     let filenames1 =
       FStarC_List.filter
         (fun fn ->
            let uu___1 = already_loaded fn in
            match uu___1 with
            | [] -> true
            | ms ->
                let uu___2 =
                  let uu___3 = FStarC_Parser_Dep.is_implementation fn in
                  if uu___3
                  then
                    let uu___4 =
                      FStarC_List.existsb
                        (fun m ->
                           Prims.not m.FStarC_Syntax_Syntax.is_interface) ms in
                    Prims.not uu___4
                  else false in
                if uu___2
                then
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            FStarC_Parser_Dep.module_name_of_file fn in
                          FStarC_Format.fmt1
                            "A non-friend dependence was already found on module %s."
                            uu___7 in
                        FStarC_Errors_Msg.text uu___6 in
                      [uu___5] in
                    (FStarC_Errors_Msg.text
                       "Friend dependences must be declared as the first dependence on a module.")
                      :: uu___4 in
                  FStarC_Errors.raise_error
                    FStarC_Class_HasRange.hasRange_range
                    (FStarC_TypeChecker_Env.get_range env2)
                    FStarC_Errors_Codes.Fatal_CyclicDependence ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic uu___3)
                else false) filenames in
     (filenames1, env2)) in
  let uu___ =
    with_tcenv_of_env env
      (fun tcenv -> scan_fragment_deps tcenv frag_or_decl) in
  match uu___ with
  | (filenames, env1) ->
      let env2 = load_fly_deps env1 filenames in (env2, filenames)
and tc_one_file_from_remaining (fly_deps : Prims.bool)
  (root : Prims.string FStar_Pervasives_Native.option)
  (remaining : Prims.string Prims.list) (env : uenv) :
  (Prims.string Prims.list * FStarC_CheckedFiles.tc_result *
    FStarC_Extraction_ML_Syntax.mlmodule FStar_Pervasives_Native.option *
    uenv)=
  let uu___ =
    match remaining with
    | intf_or_impl::rest ->
        let mname = FStarC_Parser_Dep.module_name_of_file intf_or_impl in
        let skip_solver =
          let uu___1 = is_iface_of intf_or_impl root in
          if uu___1
          then true
          else
            (let uu___2 = FStarC_Parser_Dep.is_interface intf_or_impl in
             if uu___2
             then
               match rest with
               | next::uu___3 ->
                   let uu___4 =
                     let uu___5 = FStarC_Parser_Dep.is_interface next in
                     Prims.not uu___5 in
                   (if uu___4
                    then
                      let uu___5 = FStarC_Parser_Dep.module_name_of_file next in
                      uu___5 = mname
                    else false)
               | [] -> false
             else false) in
        let uu___1 =
          tc_one_file_internal fly_deps skip_solver env intf_or_impl in
        (match uu___1 with | (m, mllib, env1) -> (rest, (m, mllib, env1)))
    | [] -> FStarC_Effect.failwith "Impossible: Empty remaining modules" in
  match uu___ with
  | (remaining1, (nmods, mllib, env1)) -> (remaining1, nmods, mllib, env1)
and tc_fold_interleave (fly_deps : Prims.bool)
  (root : Prims.string FStar_Pervasives_Native.option)
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
             tc_one_file_from_remaining fly_deps root remaining env_before in
           (match uu___2 with
            | (remaining1, nmod, mllib, env) ->
                ((let uu___4 =
                    let uu___5 = FStarC_Options.profile_group_by_decl () in
                    Prims.not uu___5 in
                  if uu___4
                  then
                    FStarC_Profiling.report_and_clear
                      (FStarC_Ident.string_of_lid
                         (nmod.FStarC_CheckedFiles.checked_module).FStarC_Syntax_Syntax.name)
                  else ());
                 tc_fold_interleave fly_deps root
                   ((FStarC_List.op_At mods [nmod]),
                     (FStarC_List.op_At mllibs (as_list env mllib)), env)
                   remaining1)))
let load_file (env : FStarC_TypeChecker_Env.env_t) (fn : Prims.string) :
  FStarC_TypeChecker_Env.env_t=
  let env1 = env_of_tcenv env in
  let uu___ = tc_one_file_internal false false env1 fn in
  match uu___ with
  | (tc_result, uu___1, env2) -> FStarC_Extraction_ML_UEnv.tcenv_of_uenv env2
let load_interface_of_current_file (env : FStarC_TypeChecker_Env.env_t)
  (fn : Prims.string) : FStarC_TypeChecker_Env.env_t=
  let uenv1 = env_of_tcenv env in
  let uu___ = tc_one_file_internal false true uenv1 fn in
  match uu___ with
  | (uu___1, uu___2, uenv2) -> FStarC_Extraction_ML_UEnv.tcenv_of_uenv uenv2
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
      ((FStarC_Extraction_ML_UEnv.tcenv_of_uenv uenv1), files)
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
      (fun uu___1 a_decl ->
         match uu___1 with
         | (tcenv1, curmod) ->
             let uu___2 =
               scan_and_load_fly_deps filename tcenv1
                 (FStar_Pervasives.Inr a_decl) in
             (match uu___2 with
              | (tcenv2, filenames) ->
                  let uu___3 =
                    tc_one_fragment is_interface curmod tcenv2
                      (FStar_Pervasives.Inr a_decl) in
                  (match uu___3 with
                   | (curmod1, tcenv3, langs) ->
                       ((tcenv3, curmod1), (langs, filenames)))))
      (tcenv, mod1) ast_decls in
  match uu___ with
  | ((tcenv1, curmod), langs_filenames) ->
      let uu___1 = FStarC_List.unzip langs_filenames in
      (match uu___1 with
       | (langs_l, filenames_l) ->
           (curmod, tcenv1, (FStarC_List.flatten langs_l),
             (FStarC_List.flatten filenames_l)))
let init_env (deps : FStarC_Parser_Dep.deps) : FStarC_TypeChecker_Env.env=
  let solver =
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
      FStarC_TypeChecker_Env.expected_post =
        (env.FStarC_TypeChecker_Env.expected_post);
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
        (env.FStarC_TypeChecker_Env.missing_decl);
      FStarC_TypeChecker_Env.iface_todo =
        (env.FStarC_TypeChecker_Env.iface_todo);
      FStarC_TypeChecker_Env.iface_hidden =
        (env.FStarC_TypeChecker_Env.iface_hidden);
      FStarC_TypeChecker_Env.iface_lids =
        (env.FStarC_TypeChecker_Env.iface_lids);
      FStarC_TypeChecker_Env.iface_val_lids =
        (env.FStarC_TypeChecker_Env.iface_val_lids)
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
      FStarC_TypeChecker_Env.expected_post =
        (env1.FStarC_TypeChecker_Env.expected_post);
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
        (env1.FStarC_TypeChecker_Env.missing_decl);
      FStarC_TypeChecker_Env.iface_todo =
        (env1.FStarC_TypeChecker_Env.iface_todo);
      FStarC_TypeChecker_Env.iface_hidden =
        (env1.FStarC_TypeChecker_Env.iface_hidden);
      FStarC_TypeChecker_Env.iface_lids =
        (env1.FStarC_TypeChecker_Env.iface_lids);
      FStarC_TypeChecker_Env.iface_val_lids =
        (env1.FStarC_TypeChecker_Env.iface_val_lids)
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
      FStarC_TypeChecker_Env.expected_post =
        (env2.FStarC_TypeChecker_Env.expected_post);
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
        (env2.FStarC_TypeChecker_Env.missing_decl);
      FStarC_TypeChecker_Env.iface_todo =
        (env2.FStarC_TypeChecker_Env.iface_todo);
      FStarC_TypeChecker_Env.iface_hidden =
        (env2.FStarC_TypeChecker_Env.iface_hidden);
      FStarC_TypeChecker_Env.iface_lids =
        (env2.FStarC_TypeChecker_Env.iface_lids);
      FStarC_TypeChecker_Env.iface_val_lids =
        (env2.FStarC_TypeChecker_Env.iface_val_lids)
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
      FStarC_TypeChecker_Env.expected_post =
        (env3.FStarC_TypeChecker_Env.expected_post);
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
        (env3.FStarC_TypeChecker_Env.missing_decl);
      FStarC_TypeChecker_Env.iface_todo =
        (env3.FStarC_TypeChecker_Env.iface_todo);
      FStarC_TypeChecker_Env.iface_hidden =
        (env3.FStarC_TypeChecker_Env.iface_hidden);
      FStarC_TypeChecker_Env.iface_lids =
        (env3.FStarC_TypeChecker_Env.iface_lids);
      FStarC_TypeChecker_Env.iface_val_lids =
        (env3.FStarC_TypeChecker_Env.iface_val_lids)
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
      FStarC_TypeChecker_Env.expected_post =
        (env4.FStarC_TypeChecker_Env.expected_post);
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
        (env4.FStarC_TypeChecker_Env.missing_decl);
      FStarC_TypeChecker_Env.iface_todo =
        (env4.FStarC_TypeChecker_Env.iface_todo);
      FStarC_TypeChecker_Env.iface_hidden =
        (env4.FStarC_TypeChecker_Env.iface_hidden);
      FStarC_TypeChecker_Env.iface_lids =
        (env4.FStarC_TypeChecker_Env.iface_lids);
      FStarC_TypeChecker_Env.iface_val_lids =
        (env4.FStarC_TypeChecker_Env.iface_val_lids)
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
   let uu___1 =
     tc_fold_interleave fly_deps FStar_Pervasives_Native.None ([], [], env)
       filenames in
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
