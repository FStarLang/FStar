open Prims
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul -> (Prims.bool * FStar_Ident.lident)) =
  fun m ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
type uenv = FStar_Extraction_ML_UEnv.uenv
let with_dsenv_of_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_Syntax_DsEnv.withenv -> ('a * FStar_TypeChecker_Env.env)
  =
  fun tcenv ->
    fun f ->
      let uu____39 = f tcenv.FStar_TypeChecker_Env.dsenv in
      match uu____39 with
      | (a, dsenv1) ->
          (a,
            (let uu___8_51 = tcenv in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___8_51.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___8_51.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___8_51.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___8_51.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___8_51.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___8_51.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___8_51.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___8_51.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___8_51.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___8_51.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___8_51.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___8_51.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___8_51.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___8_51.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___8_51.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___8_51.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___8_51.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___8_51.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___8_51.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___8_51.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___8_51.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___8_51.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___8_51.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___8_51.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___8_51.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___8_51.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___8_51.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___8_51.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___8_51.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___8_51.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___8_51.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___8_51.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___8_51.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___8_51.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___8_51.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___8_51.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___8_51.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___8_51.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___8_51.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___8_51.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___8_51.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___8_51.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___8_51.FStar_TypeChecker_Env.strict_args_tab)
             }))
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e ->
    fun f ->
      let uu____87 = f e.FStar_Extraction_ML_UEnv.env_tcenv in
      match uu____87 with
      | (a, t') ->
          (a,
            (let uu___16_99 = e in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___16_99.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___16_99.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___16_99.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___16_99.FStar_Extraction_ML_UEnv.currentModule)
             }))
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e ->
    fun f ->
      let uu____128 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f in
      match uu____128 with
      | (a, tcenv) ->
          (a,
            (let uu___24_140 = e in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___24_140.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___24_140.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___24_140.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___24_140.FStar_Extraction_ML_UEnv.currentModule)
             }))
let (push_env : uenv -> uenv) =
  fun env ->
    let uu____147 =
      with_tcenv_of_env env
        (fun tcenv ->
           let uu____155 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env" in
           ((), uu____155)) in
    FStar_Pervasives_Native.snd uu____147
let (pop_env : uenv -> uenv) =
  fun env ->
    let uu____163 =
      with_tcenv_of_env env
        (fun tcenv ->
           let uu____171 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env" in
           ((), uu____171)) in
    FStar_Pervasives_Native.snd uu____163
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env ->
    fun f ->
      let env1 = push_env env in
      let res = f env1 in let uu____198 = pop_env env1 in res
let (env_of_tcenv :
  FStar_TypeChecker_Env.env -> FStar_Extraction_ML_UEnv.uenv) =
  fun env -> FStar_Extraction_ML_UEnv.mkContext env
let (parse :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> (FStar_Syntax_Syntax.modul * uenv))
  =
  fun env ->
    fun pre_fn ->
      fun fn ->
        let uu____237 = FStar_Parser_Driver.parse_file fn in
        match uu____237 with
        | (ast, uu____254) ->
            let uu____269 =
              match pre_fn with
              | FStar_Pervasives_Native.None -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____282 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____282 with
                   | (pre_ast, uu____299) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1, decls1, uu____320), FStar_Parser_AST.Module
                           (lid2, decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____333 =
                              let uu____338 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1 in
                              with_dsenv_of_env env uu____338 in
                            (match uu____333 with
                             | (uu____347, env1) ->
                                 let uu____349 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true in
                                 with_dsenv_of_env env1 uu____349)
                        | uu____355 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n"))) in
            (match uu____269 with
             | (ast1, env1) ->
                 let uu____372 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1 in
                 with_dsenv_of_env env1 uu____372)
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps ->
    let solver1 =
      let uu____384 = FStar_Options.lax () in
      if uu____384
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___68_389 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___68_389.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___68_389.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___68_389.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___68_389.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___68_389.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_sig =
             (uu___68_389.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___68_389.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___68_389.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___68_389.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      let uu____391 =
        let uu____406 = FStar_Tactics_Interpreter.primitive_steps () in
        FStar_TypeChecker_NBE.normalize uu____406 in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____391 in
    let env1 =
      let uu___72_410 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___72_410.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___72_410.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___72_410.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___72_410.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___72_410.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___72_410.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___72_410.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___72_410.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___72_410.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___72_410.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___72_410.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___72_410.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___72_410.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___72_410.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___72_410.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___72_410.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___72_410.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___72_410.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___72_410.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___72_410.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___72_410.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___72_410.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___72_410.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___72_410.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___72_410.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___72_410.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___72_410.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___72_410.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___72_410.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___72_410.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___72_410.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___72_410.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___72_410.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___72_410.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___72_410.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___72_410.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___72_410.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___72_410.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___72_410.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___72_410.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___72_410.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___72_410.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___72_410.FStar_TypeChecker_Env.strict_args_tab)
      } in
    let env2 =
      let uu___75_412 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___75_412.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___75_412.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___75_412.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___75_412.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___75_412.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___75_412.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___75_412.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___75_412.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___75_412.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___75_412.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___75_412.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___75_412.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___75_412.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___75_412.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___75_412.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___75_412.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___75_412.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___75_412.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___75_412.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___75_412.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___75_412.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___75_412.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___75_412.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___75_412.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___75_412.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___75_412.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___75_412.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___75_412.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___75_412.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___75_412.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___75_412.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___75_412.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___75_412.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___75_412.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___75_412.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___75_412.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___75_412.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___75_412.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___75_412.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___75_412.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___75_412.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___75_412.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___75_412.FStar_TypeChecker_Env.strict_args_tab)
      } in
    let env3 =
      let uu___78_414 = env2 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___78_414.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___78_414.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___78_414.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___78_414.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___78_414.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___78_414.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___78_414.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___78_414.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___78_414.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___78_414.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___78_414.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___78_414.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___78_414.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___78_414.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___78_414.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___78_414.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___78_414.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___78_414.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___78_414.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___78_414.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___78_414.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___78_414.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___78_414.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___78_414.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___78_414.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___78_414.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___78_414.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___78_414.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___78_414.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___78_414.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___78_414.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___78_414.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___78_414.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___78_414.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___78_414.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___78_414.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___78_414.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___78_414.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___78_414.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___78_414.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___78_414.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___78_414.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___78_414.FStar_TypeChecker_Env.strict_args_tab)
      } in
    let env4 =
      let uu___81_416 = env3 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___81_416.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___81_416.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___81_416.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___81_416.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___81_416.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___81_416.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___81_416.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___81_416.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___81_416.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___81_416.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___81_416.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___81_416.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___81_416.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___81_416.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___81_416.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___81_416.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___81_416.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___81_416.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___81_416.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___81_416.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___81_416.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___81_416.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___81_416.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___81_416.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___81_416.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___81_416.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___81_416.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___81_416.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___81_416.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___81_416.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___81_416.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___81_416.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___81_416.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___81_416.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___81_416.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___81_416.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___81_416.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___81_416.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___81_416.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___81_416.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___81_416.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___81_416.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___81_416.FStar_TypeChecker_Env.strict_args_tab)
      } in
    (env4.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env4; env4
let (tc_one_fragment :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env_t ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option *
          FStar_TypeChecker_Env.env))
  =
  fun curmod ->
    fun env ->
      fun frag ->
        let fname env1 =
          let uu____451 = FStar_Options.lsp_server () in
          if uu____451
          then
            let uu____455 = FStar_TypeChecker_Env.get_range env1 in
            FStar_Range.file_of_range uu____455
          else
            (let uu____458 = FStar_Options.file_list () in
             FStar_List.hd uu____458) in
        let acceptable_mod_name modul =
          let uu____470 =
            let uu____472 = fname env in
            FStar_Parser_Dep.lowercase_module_name uu____472 in
          let uu____474 =
            let uu____476 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
            FStar_String.lowercase uu____476 in
          uu____470 = uu____474 in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____485,
               { FStar_Parser_AST.d = uu____486; FStar_Parser_AST.drange = d;
                 FStar_Parser_AST.doc = uu____488;
                 FStar_Parser_AST.quals = uu____489;
                 FStar_Parser_AST.attrs = uu____490;_}::uu____491)
              -> d
          | FStar_Parser_AST.Interface
              (uu____498,
               { FStar_Parser_AST.d = uu____499; FStar_Parser_AST.drange = d;
                 FStar_Parser_AST.doc = uu____501;
                 FStar_Parser_AST.quals = uu____502;
                 FStar_Parser_AST.attrs = uu____503;_}::uu____504,
               uu____505)
              -> d
          | uu____514 -> FStar_Range.dummyRange in
        let uu____515 = FStar_Parser_Driver.parse_fragment frag in
        match uu____515 with
        | FStar_Parser_Driver.Empty -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____527 =
              let uu____532 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____532 in
            (match uu____527 with
             | (ast_modul1, env1) ->
                 let uu____553 =
                   let uu____558 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1 in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____558 in
                 (match uu____553 with
                  | (modul, env2) ->
                      ((let uu____579 =
                          let uu____581 = acceptable_mod_name modul in
                          Prims.op_Negation uu____581 in
                        if uu____579
                        then
                          let msg =
                            let uu____586 =
                              let uu____588 = fname env2 in
                              FStar_Parser_Dep.module_name_of_file uu____588 in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____586 in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____594 =
                          let uu____605 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv in
                          if uu____605
                          then ((modul, []), env2)
                          else
                            (let uu____628 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul in
                             match uu____628 with | (m, i, e) -> ((m, i), e)) in
                        match uu____594 with
                        | ((modul1, uu____669), env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None ->
                 let uu____692 = FStar_List.hd ast_decls in
                 (match uu____692 with
                  | { FStar_Parser_AST.d = uu____699;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____701;
                      FStar_Parser_AST.quals = uu____702;
                      FStar_Parser_AST.attrs = uu____703;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____715 =
                   FStar_Util.fold_map
                     (fun env1 ->
                        fun a_decl ->
                          let uu____733 =
                            let uu____740 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____740 in
                          match uu____733 with
                          | (decls, env2) -> (env2, decls)) env ast_decls in
                 (match uu____715 with
                  | (env1, ast_decls_l) ->
                      let uu____790 =
                        let uu____795 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l) in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____795 in
                      (match uu____790 with
                       | (sigelts, env2) ->
                           let uu____815 =
                             let uu____824 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv in
                             if uu____824
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts in
                           (match uu____815 with
                            | (modul1, uu____846, env3) ->
                                ((FStar_Pervasives_Native.Some modul1), env3)))))
let (load_interface_decls :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env_t) =
  fun env ->
    fun interface_file_name ->
      let r =
        FStar_Parser_ParseIt.parse
          (FStar_Parser_ParseIt.Filename interface_file_name) in
      match r with
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____870)),
           uu____871)
          ->
          let uu____894 =
            let uu____899 =
              FStar_ToSyntax_Interleave.initialize_interface l decls in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____899 in
          FStar_Pervasives_Native.snd uu____894
      | FStar_Parser_ParseIt.ASTFragment uu____911 ->
          let uu____923 =
            let uu____929 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name in
            (FStar_Errors.Fatal_ParseErrors, uu____929) in
          FStar_Errors.raise_err uu____923
      | FStar_Parser_ParseIt.ParseError (err, msg, rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____939 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
let (emit : FStar_Extraction_ML_Syntax.mllib Prims.list -> unit) =
  fun mllibs ->
    let opt = FStar_Options.codegen () in
    if opt <> FStar_Pervasives_Native.None
    then
      let ext =
        match opt with
        | FStar_Pervasives_Native.Some (FStar_Options.FSharp) -> ".fs"
        | FStar_Pervasives_Native.Some (FStar_Options.OCaml) -> ".ml"
        | FStar_Pervasives_Native.Some (FStar_Options.Plugin) -> ".ml"
        | FStar_Pervasives_Native.Some (FStar_Options.Kremlin) -> ".krml"
        | uu____964 -> failwith "Unrecognized option" in
      match opt with
      | FStar_Pervasives_Native.Some (FStar_Options.FSharp) ->
          let outdir = FStar_Options.output_dir () in
          FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
            mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.OCaml) ->
          let outdir = FStar_Options.output_dir () in
          FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
            mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.Plugin) ->
          let outdir = FStar_Options.output_dir () in
          FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
            mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.Kremlin) ->
          let programs =
            FStar_List.collect FStar_Extraction_Kremlin.translate mllibs in
          let bin = (FStar_Extraction_Kremlin.current_version, programs) in
          (match programs with
           | (name, uu____989)::[] ->
               let uu____992 =
                 FStar_Options.prepend_output_dir (Prims.op_Hat name ext) in
               FStar_Util.save_value_to_file uu____992 bin
           | uu____994 ->
               let uu____997 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____997 bin)
      | uu____1000 -> failwith "Unrecognized option"
    else ()
let (tc_one_file :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        FStar_Parser_Dep.parsing_data ->
          (FStar_CheckedFiles.tc_result * FStar_Extraction_ML_Syntax.mllib
            FStar_Pervasives_Native.option * uenv))
  =
  fun env ->
    fun pre_fn ->
      fun fn ->
        fun parsing_data ->
          FStar_Ident.reset_gensym ();
          (let maybe_restore_opts uu____1057 =
             let uu____1058 =
               let uu____1060 = FStar_Options.interactive () in
               Prims.op_Negation uu____1060 in
             if uu____1058
             then
               let uu____1063 = FStar_Options.restore_cmd_line_options true in
               FStar_All.pipe_right uu____1063 (fun a1 -> ())
             else () in
           let post_smt_encoding uu____1072 = FStar_SMTEncoding_Z3.refresh () in
           let maybe_extract_mldefs tcmod env1 =
             let uu____1091 =
               (let uu____1095 = FStar_Options.codegen () in
                uu____1095 = FStar_Pervasives_Native.None) ||
                 (let uu____1101 =
                    FStar_Options.should_extract
                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str in
                  Prims.op_Negation uu____1101) in
             if uu____1091
             then (FStar_Pervasives_Native.None, Prims.int_zero)
             else
               FStar_Util.record_time
                 (fun uu____1123 ->
                    let uu____1124 =
                      FStar_Extraction_ML_Modul.extract env1 tcmod in
                    match uu____1124 with | (uu____1133, defs) -> defs) in
           let maybe_extract_ml_iface tcmod env1 =
             let uu____1155 =
               let uu____1157 = FStar_Options.codegen () in
               uu____1157 = FStar_Pervasives_Native.None in
             if uu____1155
             then (env1, Prims.int_zero)
             else
               (let uu____1172 =
                  FStar_Util.record_time
                    (fun uu____1187 ->
                       FStar_Extraction_ML_Modul.extract_iface env1 tcmod) in
                match uu____1172 with
                | ((env2, _extracted_iface), iface_extract_time) ->
                    (env2, iface_extract_time)) in
           let tc_source_file uu____1216 =
             let uu____1217 = parse env pre_fn fn in
             match uu____1217 with
             | (fmod, env1) ->
                 let mii =
                   FStar_Syntax_DsEnv.inclusion_info
                     (env1.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                     fmod.FStar_Syntax_Syntax.name in
                 let check_mod uu____1246 =
                   let uu____1247 =
                     FStar_Util.record_time
                       (fun uu____1282 ->
                          with_tcenv_of_env env1
                            (fun tcenv ->
                               (match tcenv.FStar_TypeChecker_Env.gamma with
                                | [] -> ()
                                | uu____1302 ->
                                    failwith
                                      "Impossible: gamma contains leaked names");
                               (let uu____1306 =
                                  FStar_TypeChecker_Tc.check_module tcenv
                                    fmod (FStar_Util.is_some pre_fn) in
                                match uu____1306 with
                                | (modul, env2) ->
                                    (maybe_restore_opts ();
                                     (let smt_decls =
                                        let uu____1336 =
                                          let uu____1338 =
                                            FStar_Options.lax () in
                                          Prims.op_Negation uu____1338 in
                                        if uu____1336
                                        then
                                          let smt_decls =
                                            FStar_SMTEncoding_Encode.encode_modul
                                              env2 modul in
                                          (post_smt_encoding (); smt_decls)
                                        else ([], []) in
                                      ((modul, smt_decls), env2)))))) in
                   match uu____1247 with
                   | (((tcmod, smt_decls), env2), tc_time) ->
                       let uu____1425 =
                         with_env env2 (maybe_extract_mldefs tcmod) in
                       (match uu____1425 with
                        | (extracted_defs, extract_time) ->
                            let uu____1456 =
                              with_env env2 (maybe_extract_ml_iface tcmod) in
                            (match uu____1456 with
                             | (env3, iface_extraction_time) ->
                                 ({
                                    FStar_CheckedFiles.checked_module = tcmod;
                                    FStar_CheckedFiles.mii = mii;
                                    FStar_CheckedFiles.smt_decls = smt_decls;
                                    FStar_CheckedFiles.tc_time = tc_time;
                                    FStar_CheckedFiles.extraction_time =
                                      (extract_time + iface_extraction_time)
                                  }, extracted_defs, env3))) in
                 let uu____1481 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ())) in
                 if uu____1481
                 then
                   let uu____1492 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1492
                     check_mod
                 else check_mod () in
           let uu____1504 =
             let uu____1506 = FStar_Options.cache_off () in
             Prims.op_Negation uu____1506 in
           if uu____1504
           then
             let uu____1517 =
               FStar_CheckedFiles.load_module_from_cache env fn in
             match uu____1517 with
             | FStar_Pervasives_Native.None ->
                 ((let uu____1529 =
                     let uu____1531 = FStar_Parser_Dep.module_name_of_file fn in
                     FStar_Options.should_be_already_cached uu____1531 in
                   if uu____1529
                   then
                     let uu____1534 =
                       let uu____1540 =
                         FStar_Util.format1
                           "Expected %s to already be checked" fn in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____1540) in
                     FStar_Errors.raise_err uu____1534
                   else ());
                  (let uu____1547 =
                     (let uu____1551 = FStar_Options.codegen () in
                      FStar_Option.isSome uu____1551) &&
                       (FStar_Options.cmi ()) in
                   if uu____1547
                   then
                     let uu____1555 =
                       let uu____1561 =
                         FStar_Util.format1
                           "Cross-module inlining expects all modules to be checked first; %s was not checked"
                           fn in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____1561) in
                     FStar_Errors.raise_err uu____1555
                   else ());
                  (let uu____1567 = tc_source_file () in
                   match uu____1567 with
                   | (tc_result, mllib, env1) ->
                       ((let uu____1592 =
                           (let uu____1596 = FStar_Errors.get_err_count () in
                            uu____1596 = Prims.int_zero) &&
                             ((FStar_Options.lax ()) ||
                                (FStar_Options.should_verify
                                   ((tc_result.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str)) in
                         if uu____1592
                         then
                           FStar_CheckedFiles.store_module_to_cache env1 fn
                             parsing_data tc_result
                         else ());
                        (tc_result, mllib, env1))))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.FStar_CheckedFiles.checked_module in
                 let smt_decls = tc_result.FStar_CheckedFiles.smt_decls in
                 ((let uu____1615 =
                     FStar_Options.dump_module
                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str in
                   if uu____1615
                   then
                     let uu____1618 =
                       FStar_Syntax_Print.modul_to_string tcmod in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____1618
                   else ());
                  (let extend_tcenv tcmod1 tcenv =
                     let uu____1638 =
                       let uu____1643 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                           tc_result.FStar_CheckedFiles.mii
                           (FStar_TypeChecker_Normalize.erase_universes tcenv) in
                       FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                         uu____1643 in
                     match uu____1638 with
                     | (uu____1659, tcenv1) ->
                         let env1 =
                           FStar_TypeChecker_Tc.load_checked_module tcenv1
                             tcmod1 in
                         (maybe_restore_opts ();
                          (let uu____1664 =
                             let uu____1666 = FStar_Options.lax () in
                             Prims.op_Negation uu____1666 in
                           if uu____1664
                           then
                             (FStar_SMTEncoding_Encode.encode_modul_from_cache
                                env1 tcmod1.FStar_Syntax_Syntax.name
                                smt_decls;
                              post_smt_encoding ())
                           else ());
                          ((), env1)) in
                   let env1 =
                     FStar_Options.profile
                       (fun uu____1675 ->
                          let uu____1676 =
                            with_tcenv_of_env env (extend_tcenv tcmod) in
                          FStar_All.pipe_right uu____1676
                            FStar_Pervasives_Native.snd)
                       (fun uu____1686 ->
                          FStar_Util.format1
                            "Extending environment with module %s"
                            (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str) in
                   let mllib =
                     let uu____1691 =
                       ((let uu____1695 = FStar_Options.codegen () in
                         uu____1695 <> FStar_Pervasives_Native.None) &&
                          (FStar_Options.should_extract
                             (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                         &&
                         ((Prims.op_Negation
                             tcmod.FStar_Syntax_Syntax.is_interface)
                            ||
                            (let uu____1701 = FStar_Options.codegen () in
                             uu____1701 =
                               (FStar_Pervasives_Native.Some
                                  FStar_Options.Kremlin))) in
                     if uu____1691
                     then
                       with_env env1
                         (fun env2 ->
                            let uu____1716 = maybe_extract_mldefs tcmod env2 in
                            match uu____1716 with
                            | (extracted_defs, _extraction_time) ->
                                extracted_defs)
                     else FStar_Pervasives_Native.None in
                   let uu____1736 =
                     with_env env1 (maybe_extract_ml_iface tcmod) in
                   match uu____1736 with
                   | (env2, _time) -> (tc_result, mllib, env2)))
           else
             (let uu____1763 = tc_source_file () in
              match uu____1763 with
              | (tc_result, mllib, env1) -> (tc_result, mllib, env1)))
let (tc_one_file_for_ide :
  FStar_TypeChecker_Env.env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        FStar_Parser_Dep.parsing_data ->
          (FStar_CheckedFiles.tc_result * FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun pre_fn ->
      fun fn ->
        fun parsing_data ->
          let env1 = env_of_tcenv env in
          let uu____1827 = tc_one_file env1 pre_fn fn parsing_data in
          match uu____1827 with
          | (tc_result, uu____1841, env2) ->
              (tc_result, (env2.FStar_Extraction_ML_UEnv.env_tcenv))
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf ->
    fun impl ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1869 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1869 ["fsti"; "fsi"]))
        &&
        (let uu____1878 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1878 ["fst"; "fs"])
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      FStar_Parser_Dep.deps ->
        (Prims.string Prims.list * FStar_CheckedFiles.tc_result Prims.list *
          FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option *
          uenv))
  =
  fun remaining ->
    fun env ->
      fun deps ->
        let uu____1923 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____1968 =
                let uu____1977 =
                  FStar_All.pipe_right impl
                    (FStar_Parser_Dep.parsing_data_of deps) in
                tc_one_file env (FStar_Pervasives_Native.Some intf) impl
                  uu____1977 in
              (match uu____1968 with
               | (m, mllib, env1) -> (remaining1, ([m], mllib, env1)))
          | intf_or_impl::remaining1 ->
              let uu____2028 =
                let uu____2037 =
                  FStar_All.pipe_right intf_or_impl
                    (FStar_Parser_Dep.parsing_data_of deps) in
                tc_one_file env FStar_Pervasives_Native.None intf_or_impl
                  uu____2037 in
              (match uu____2028 with
               | (m, mllib, env1) -> (remaining1, ([m], mllib, env1)))
          | [] -> ([], ([], FStar_Pervasives_Native.None, env)) in
        match uu____1923 with
        | (remaining1, (nmods, mllib, env1)) ->
            (remaining1, nmods, mllib, env1)
let rec (tc_fold_interleave :
  FStar_Parser_Dep.deps ->
    (FStar_CheckedFiles.tc_result Prims.list *
      FStar_Extraction_ML_Syntax.mllib Prims.list * uenv) ->
      Prims.string Prims.list ->
        (FStar_CheckedFiles.tc_result Prims.list *
          FStar_Extraction_ML_Syntax.mllib Prims.list * uenv))
  =
  fun deps ->
    fun acc ->
      fun remaining ->
        let as_list uu___0_2211 =
          match uu___0_2211 with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some l -> [l] in
        match remaining with
        | [] -> acc
        | uu____2228 ->
            let uu____2232 = acc in
            (match uu____2232 with
             | (mods, mllibs, env) ->
                 let uu____2264 =
                   tc_one_file_from_remaining remaining env deps in
                 (match uu____2264 with
                  | (remaining1, nmods, mllib, env1) ->
                      tc_fold_interleave deps
                        ((FStar_List.append mods nmods),
                          (FStar_List.append mllibs (as_list mllib)), env1)
                        remaining1))
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      (FStar_CheckedFiles.tc_result Prims.list * uenv * (uenv -> uenv)))
  =
  fun filenames ->
    fun dep_graph1 ->
      (let uu____2341 = FStar_Options.debug_any () in
       if uu____2341
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____2349 =
             let uu____2351 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file) in
             FStar_String.concat " " uu____2351 in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____2349))
       else ());
      (let env =
         let uu____2367 = init_env dep_graph1 in
         FStar_Extraction_ML_UEnv.mkContext uu____2367 in
       let uu____2368 = tc_fold_interleave dep_graph1 ([], [], env) filenames in
       match uu____2368 with
       | (all_mods, mllibs, env1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____2412 =
                 with_tcenv_of_env env2
                   (fun tcenv ->
                      (let uu____2421 =
                         (FStar_Options.interactive ()) &&
                           (let uu____2424 = FStar_Errors.get_err_count () in
                            uu____2424 = Prims.int_zero) in
                       if uu____2421
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv)) in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2412 in
             (all_mods, env1, solver_refresh))))