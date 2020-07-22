open Prims
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul -> (Prims.bool * FStar_Ident.lid)) =
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
      let uu____36 = f tcenv.FStar_TypeChecker_Env.dsenv in
      match uu____36 with
      | (a1, dsenv) ->
          (a1,
            (let uu___9_48 = tcenv in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___9_48.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___9_48.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___9_48.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___9_48.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___9_48.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___9_48.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___9_48.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___9_48.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___9_48.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___9_48.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___9_48.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___9_48.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___9_48.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___9_48.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___9_48.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___9_48.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___9_48.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___9_48.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (uu___9_48.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___9_48.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___9_48.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___9_48.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___9_48.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___9_48.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___9_48.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___9_48.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___9_48.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___9_48.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___9_48.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___9_48.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___9_48.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___9_48.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___9_48.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___9_48.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___9_48.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___9_48.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___9_48.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___9_48.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___9_48.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___9_48.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___9_48.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___9_48.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv;
               FStar_TypeChecker_Env.nbe =
                 (uu___9_48.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___9_48.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___9_48.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (uu___9_48.FStar_TypeChecker_Env.enable_defer_to_tac)
             }))
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e ->
    fun f ->
      let uu____83 =
        let uu____88 = FStar_Extraction_ML_UEnv.tcenv_of_uenv e in f uu____88 in
      match uu____83 with
      | (a1, t') ->
          let uu____95 = FStar_Extraction_ML_UEnv.set_tcenv e t' in
          (a1, uu____95)
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e ->
    fun f ->
      let uu____123 =
        let uu____128 = FStar_Extraction_ML_UEnv.tcenv_of_uenv e in
        with_dsenv_of_tcenv uu____128 f in
      match uu____123 with
      | (a1, tcenv) ->
          let uu____135 = FStar_Extraction_ML_UEnv.set_tcenv e tcenv in
          (a1, uu____135)
let (push_env : uenv -> uenv) =
  fun env ->
    let uu____141 =
      with_tcenv_of_env env
        (fun tcenv ->
           let uu____149 =
             let uu____150 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
             FStar_TypeChecker_Env.push uu____150 "top-level: push_env" in
           ((), uu____149)) in
    FStar_Pervasives_Native.snd uu____141
let (pop_env : uenv -> uenv) =
  fun env ->
    let uu____156 =
      with_tcenv_of_env env
        (fun tcenv ->
           let uu____164 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env" in
           ((), uu____164)) in
    FStar_Pervasives_Native.snd uu____156
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env ->
    fun f ->
      let env1 = push_env env in
      let res = f env1 in let uu____189 = pop_env env1 in res
let (env_of_tcenv :
  FStar_TypeChecker_Env.env -> FStar_Extraction_ML_UEnv.uenv) =
  fun env -> FStar_Extraction_ML_UEnv.new_uenv env
let (parse :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> (FStar_Syntax_Syntax.modul * uenv))
  =
  fun env ->
    fun pre_fn ->
      fun fn ->
        let uu____222 = FStar_Parser_Driver.parse_file fn in
        match uu____222 with
        | (ast, uu____238) ->
            let uu____251 =
              match pre_fn with
              | FStar_Pervasives_Native.None -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____261 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____261 with
                   | (pre_ast, uu____277) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1, decls1, uu____296), FStar_Parser_AST.Module
                           (lid2, decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____307 =
                              let uu____312 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1 in
                              with_dsenv_of_env env uu____312 in
                            (match uu____307 with
                             | (uu____321, env1) ->
                                 let uu____323 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true in
                                 with_dsenv_of_env env1 uu____323)
                        | uu____328 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n"))) in
            (match uu____251 with
             | (ast1, env1) ->
                 let uu____343 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1 in
                 with_dsenv_of_env env1 uu____343)
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps ->
    let solver =
      let uu____354 = FStar_Options.lax () in
      if uu____354
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___65_356 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___65_356.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___65_356.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___65_356.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___65_356.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___65_356.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_sig =
             (uu___65_356.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess = FStar_Tactics_Hooks.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___65_356.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___65_356.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___65_356.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      let uu____358 =
        let uu____373 = FStar_Tactics_Interpreter.primitive_steps () in
        FStar_TypeChecker_NBE.normalize uu____373 in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver
        FStar_Parser_Const.prims_lid uu____358 in
    let env1 =
      let uu___69_377 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___69_377.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___69_377.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___69_377.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___69_377.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___69_377.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___69_377.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___69_377.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___69_377.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___69_377.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___69_377.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___69_377.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___69_377.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___69_377.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___69_377.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___69_377.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___69_377.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___69_377.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___69_377.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___69_377.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___69_377.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___69_377.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___69_377.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___69_377.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___69_377.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___69_377.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___69_377.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___69_377.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___69_377.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___69_377.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___69_377.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___69_377.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___69_377.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___69_377.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___69_377.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___69_377.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook = FStar_Tactics_Hooks.synthesize;
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___69_377.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice =
          (uu___69_377.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___69_377.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___69_377.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___69_377.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___69_377.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___69_377.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___69_377.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___69_377.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___69_377.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___69_377.FStar_TypeChecker_Env.enable_defer_to_tac)
      } in
    let env2 =
      let uu___72_379 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___72_379.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___72_379.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___72_379.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___72_379.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___72_379.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___72_379.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___72_379.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___72_379.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___72_379.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___72_379.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___72_379.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___72_379.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___72_379.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___72_379.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___72_379.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___72_379.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___72_379.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___72_379.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___72_379.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___72_379.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___72_379.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___72_379.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___72_379.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___72_379.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___72_379.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___72_379.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___72_379.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___72_379.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___72_379.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___72_379.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___72_379.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___72_379.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___72_379.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___72_379.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___72_379.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___72_379.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          FStar_Tactics_Hooks.solve_implicits;
        FStar_TypeChecker_Env.splice =
          (uu___72_379.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___72_379.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___72_379.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___72_379.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___72_379.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___72_379.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___72_379.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___72_379.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___72_379.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___72_379.FStar_TypeChecker_Env.enable_defer_to_tac)
      } in
    let env3 =
      let uu___75_381 = env2 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___75_381.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___75_381.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___75_381.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___75_381.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___75_381.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___75_381.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___75_381.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___75_381.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___75_381.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___75_381.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___75_381.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___75_381.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___75_381.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___75_381.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___75_381.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___75_381.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___75_381.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___75_381.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___75_381.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___75_381.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___75_381.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___75_381.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___75_381.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___75_381.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___75_381.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___75_381.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___75_381.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___75_381.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___75_381.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___75_381.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___75_381.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___75_381.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___75_381.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___75_381.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___75_381.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___75_381.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___75_381.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Hooks.splice;
        FStar_TypeChecker_Env.mpreprocess =
          (uu___75_381.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___75_381.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___75_381.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___75_381.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___75_381.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___75_381.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___75_381.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___75_381.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___75_381.FStar_TypeChecker_Env.enable_defer_to_tac)
      } in
    let env4 =
      let uu___78_383 = env3 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___78_383.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___78_383.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___78_383.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___78_383.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___78_383.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___78_383.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___78_383.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___78_383.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___78_383.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___78_383.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___78_383.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___78_383.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___78_383.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___78_383.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___78_383.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___78_383.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___78_383.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___78_383.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___78_383.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___78_383.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___78_383.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___78_383.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___78_383.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___78_383.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___78_383.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___78_383.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___78_383.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___78_383.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___78_383.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___78_383.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___78_383.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___78_383.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___78_383.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___78_383.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___78_383.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___78_383.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___78_383.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice =
          (uu___78_383.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess = FStar_Tactics_Hooks.mpreprocess;
        FStar_TypeChecker_Env.postprocess =
          (uu___78_383.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___78_383.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___78_383.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___78_383.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___78_383.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___78_383.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___78_383.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___78_383.FStar_TypeChecker_Env.enable_defer_to_tac)
      } in
    let env5 =
      let uu___81_385 = env4 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___81_385.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___81_385.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___81_385.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___81_385.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___81_385.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___81_385.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___81_385.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___81_385.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___81_385.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___81_385.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___81_385.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___81_385.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___81_385.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___81_385.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___81_385.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___81_385.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___81_385.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___81_385.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___81_385.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___81_385.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___81_385.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___81_385.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___81_385.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___81_385.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___81_385.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___81_385.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___81_385.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___81_385.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___81_385.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___81_385.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___81_385.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___81_385.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___81_385.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___81_385.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___81_385.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___81_385.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___81_385.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice =
          (uu___81_385.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___81_385.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess = FStar_Tactics_Hooks.postprocess;
        FStar_TypeChecker_Env.identifier_info =
          (uu___81_385.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___81_385.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___81_385.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___81_385.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___81_385.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___81_385.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___81_385.FStar_TypeChecker_Env.enable_defer_to_tac)
      } in
    (env5.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env5; env5
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
          let uu____418 = FStar_Options.lsp_server () in
          if uu____418
          then
            let uu____419 = FStar_TypeChecker_Env.get_range env1 in
            FStar_Range.file_of_range uu____419
          else
            (let uu____421 = FStar_Options.file_list () in
             FStar_List.hd uu____421) in
        let acceptable_mod_name modul =
          let uu____430 =
            let uu____431 = fname env in
            FStar_Parser_Dep.lowercase_module_name uu____431 in
          let uu____432 =
            let uu____433 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
            FStar_String.lowercase uu____433 in
          uu____430 = uu____432 in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____440,
               { FStar_Parser_AST.d = uu____441; FStar_Parser_AST.drange = d;
                 FStar_Parser_AST.quals = uu____443;
                 FStar_Parser_AST.attrs = uu____444;_}::uu____445)
              -> d
          | FStar_Parser_AST.Interface
              (uu____450,
               { FStar_Parser_AST.d = uu____451; FStar_Parser_AST.drange = d;
                 FStar_Parser_AST.quals = uu____453;
                 FStar_Parser_AST.attrs = uu____454;_}::uu____455,
               uu____456)
              -> d
          | uu____461 -> FStar_Range.dummyRange in
        let uu____462 = FStar_Parser_Driver.parse_fragment frag in
        match uu____462 with
        | FStar_Parser_Driver.Empty -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____474 =
              let uu____479 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____479 in
            (match uu____474 with
             | (ast_modul1, env1) ->
                 let uu____499 =
                   let uu____504 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1 in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____504 in
                 (match uu____499 with
                  | (modul, env2) ->
                      ((let uu____525 =
                          let uu____526 = acceptable_mod_name modul in
                          Prims.op_Negation uu____526 in
                        if uu____525
                        then
                          let msg =
                            let uu____528 =
                              let uu____529 = fname env2 in
                              FStar_Parser_Dep.module_name_of_file uu____529 in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____528 in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____531 =
                          let uu____536 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv in
                          if uu____536
                          then (modul, env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul in
                        match uu____531 with
                        | (modul1, env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None ->
                 let uu____561 = FStar_List.hd ast_decls in
                 (match uu____561 with
                  | { FStar_Parser_AST.d = uu____568;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.quals = uu____570;
                      FStar_Parser_AST.attrs = uu____571;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____579 =
                   FStar_Util.fold_map
                     (fun env1 ->
                        fun a_decl ->
                          let uu____597 =
                            let uu____604 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                modul.FStar_Syntax_Syntax.name a_decl in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____604 in
                          match uu____597 with
                          | (decls, env2) -> (env2, decls)) env ast_decls in
                 (match uu____579 with
                  | (env1, ast_decls_l) ->
                      let uu____654 =
                        let uu____659 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l) in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____659 in
                      (match uu____654 with
                       | (sigelts, env2) ->
                           let uu____679 =
                             let uu____688 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv in
                             if uu____688
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts in
                           (match uu____679 with
                            | (modul1, uu____707, env3) ->
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
          (FStar_Util.Inl (FStar_Parser_AST.Interface (l, decls, uu____728)),
           uu____729)
          ->
          let uu____748 =
            let uu____753 =
              FStar_ToSyntax_Interleave.initialize_interface l decls in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____753 in
          FStar_Pervasives_Native.snd uu____748
      | FStar_Parser_ParseIt.ASTFragment uu____765 ->
          let uu____776 =
            let uu____781 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name in
            (FStar_Errors.Fatal_ParseErrors, uu____781) in
          FStar_Errors.raise_err uu____776
      | FStar_Parser_ParseIt.ParseError (err, msg, rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____785 ->
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
        | uu____801 -> failwith "Unrecognized option" in
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
           | (name, uu____820)::[] ->
               let uu____821 =
                 FStar_Options.prepend_output_dir (Prims.op_Hat name ext) in
               FStar_Util.save_value_to_file uu____821 bin
           | uu____822 ->
               let uu____825 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Util.save_value_to_file uu____825 bin)
      | uu____826 -> failwith "Unrecognized option"
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
          (let maybe_restore_opts uu____876 =
             let uu____877 =
               let uu____878 = FStar_Options.interactive () in
               Prims.op_Negation uu____878 in
             if uu____877
             then
               let uu____879 = FStar_Options.restore_cmd_line_options true in
               FStar_All.pipe_right uu____879 (fun uu____880 -> ())
             else () in
           let post_smt_encoding uu____887 = FStar_SMTEncoding_Z3.refresh () in
           let maybe_extract_mldefs tcmod env1 =
             let uu____905 =
               (let uu____908 = FStar_Options.codegen () in
                uu____908 = FStar_Pervasives_Native.None) ||
                 (let uu____914 =
                    let uu____915 =
                      FStar_Ident.string_of_lid
                        tcmod.FStar_Syntax_Syntax.name in
                    FStar_Options.should_extract uu____915 in
                  Prims.op_Negation uu____914) in
             if uu____905
             then (FStar_Pervasives_Native.None, Prims.int_zero)
             else
               FStar_Util.record_time
                 (fun uu____928 ->
                    with_env env1
                      (fun env2 ->
                         let uu____936 =
                           FStar_Extraction_ML_Modul.extract env2 tcmod in
                         match uu____936 with | (uu____945, defs) -> defs)) in
           let maybe_extract_ml_iface tcmod env1 =
             let uu____966 =
               let uu____967 = FStar_Options.codegen () in
               uu____967 = FStar_Pervasives_Native.None in
             if uu____966
             then (env1, Prims.int_zero)
             else
               FStar_Util.record_time
                 (fun uu____981 ->
                    let uu____982 =
                      with_env env1
                        (fun env2 ->
                           FStar_Extraction_ML_Modul.extract_iface env2 tcmod) in
                    match uu____982 with | (env2, uu____994) -> env2) in
           let tc_source_file uu____1008 =
             let uu____1009 = parse env pre_fn fn in
             match uu____1009 with
             | (fmod, env1) ->
                 let mii =
                   let uu____1025 =
                     let uu____1026 =
                       FStar_Extraction_ML_UEnv.tcenv_of_uenv env1 in
                     uu____1026.FStar_TypeChecker_Env.dsenv in
                   FStar_Syntax_DsEnv.inclusion_info uu____1025
                     fmod.FStar_Syntax_Syntax.name in
                 let check_mod uu____1040 =
                   let check env2 =
                     with_tcenv_of_env env2
                       (fun tcenv ->
                          (match tcenv.FStar_TypeChecker_Env.gamma with
                           | [] -> ()
                           | uu____1080 ->
                               failwith
                                 "Impossible: gamma contains leaked names");
                          (let uu____1083 =
                             FStar_TypeChecker_Tc.check_module tcenv fmod
                               (FStar_Util.is_some pre_fn) in
                           match uu____1083 with
                           | (modul, env3) ->
                               (maybe_restore_opts ();
                                (let smt_decls =
                                   let uu____1112 =
                                     let uu____1113 = FStar_Options.lax () in
                                     Prims.op_Negation uu____1113 in
                                   if uu____1112
                                   then
                                     let smt_decls =
                                       FStar_SMTEncoding_Encode.encode_modul
                                         env3 modul in
                                     (post_smt_encoding (); smt_decls)
                                   else ([], []) in
                                 ((modul, smt_decls), env3))))) in
                   let uu____1147 =
                     let uu____1162 =
                       let uu____1165 =
                         FStar_Ident.string_of_lid
                           fmod.FStar_Syntax_Syntax.name in
                       FStar_Pervasives_Native.Some uu____1165 in
                     FStar_Profiling.profile (fun uu____1181 -> check env1)
                       uu____1162 "FStar.Universal.tc_source_file" in
                   match uu____1147 with
                   | ((tcmod, smt_decls), env2) ->
                       let tc_time = Prims.int_zero in
                       let uu____1216 = maybe_extract_mldefs tcmod env2 in
                       (match uu____1216 with
                        | (extracted_defs, extract_time) ->
                            let uu____1237 =
                              maybe_extract_ml_iface tcmod env2 in
                            (match uu____1237 with
                             | (env3, iface_extraction_time) ->
                                 ({
                                    FStar_CheckedFiles.checked_module = tcmod;
                                    FStar_CheckedFiles.mii = mii;
                                    FStar_CheckedFiles.smt_decls = smt_decls;
                                    FStar_CheckedFiles.tc_time = tc_time;
                                    FStar_CheckedFiles.extraction_time =
                                      (extract_time + iface_extraction_time)
                                  }, extracted_defs, env3))) in
                 let uu____1254 =
                   (let uu____1257 =
                      FStar_Ident.string_of_lid fmod.FStar_Syntax_Syntax.name in
                    FStar_Options.should_verify uu____1257) &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ())) in
                 if uu____1254
                 then
                   let uu____1266 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1266
                     check_mod
                 else check_mod () in
           let uu____1276 =
             let uu____1277 = FStar_Options.cache_off () in
             Prims.op_Negation uu____1277 in
           if uu____1276
           then
             let r = FStar_CheckedFiles.load_module_from_cache env fn in
             let r1 =
               let uu____1292 =
                 (FStar_Options.force ()) &&
                   (FStar_Options.should_check_file fn) in
               if uu____1292 then FStar_Pervasives_Native.None else r in
             match r1 with
             | FStar_Pervasives_Native.None ->
                 ((let uu____1305 =
                     let uu____1306 = FStar_Parser_Dep.module_name_of_file fn in
                     FStar_Options.should_be_already_cached uu____1306 in
                   if uu____1305
                   then
                     let uu____1307 =
                       let uu____1312 =
                         FStar_Util.format1
                           "Expected %s to already be checked" fn in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____1312) in
                     FStar_Errors.raise_err uu____1307
                   else ());
                  (let uu____1315 =
                     (let uu____1318 = FStar_Options.codegen () in
                      FStar_Option.isSome uu____1318) &&
                       (FStar_Options.cmi ()) in
                   if uu____1315
                   then
                     let uu____1321 =
                       let uu____1326 =
                         FStar_Util.format1
                           "Cross-module inlining expects all modules to be checked first; %s was not checked"
                           fn in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____1326) in
                     FStar_Errors.raise_err uu____1321
                   else ());
                  (let uu____1328 = tc_source_file () in
                   match uu____1328 with
                   | (tc_result, mllib, env1) ->
                       ((let uu____1353 =
                           (let uu____1356 = FStar_Errors.get_err_count () in
                            uu____1356 = Prims.int_zero) &&
                             ((FStar_Options.lax ()) ||
                                (let uu____1358 =
                                   FStar_Ident.string_of_lid
                                     (tc_result.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name in
                                 FStar_Options.should_verify uu____1358)) in
                         if uu____1353
                         then
                           FStar_CheckedFiles.store_module_to_cache env1 fn
                             parsing_data tc_result
                         else ());
                        (tc_result, mllib, env1))))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.FStar_CheckedFiles.checked_module in
                 let smt_decls = tc_result.FStar_CheckedFiles.smt_decls in
                 ((let uu____1372 =
                     let uu____1373 =
                       FStar_Ident.string_of_lid
                         tcmod.FStar_Syntax_Syntax.name in
                     FStar_Options.dump_module uu____1373 in
                   if uu____1372
                   then
                     let uu____1374 =
                       FStar_Syntax_Print.modul_to_string tcmod in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____1374
                   else ());
                  (let extend_tcenv tcmod1 tcenv =
                     let uu____1391 =
                       let uu____1396 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                           tc_result.FStar_CheckedFiles.mii
                           (FStar_TypeChecker_Normalize.erase_universes tcenv) in
                       FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                         uu____1396 in
                     match uu____1391 with
                     | (uu____1412, tcenv1) ->
                         let env1 =
                           FStar_TypeChecker_Tc.load_checked_module tcenv1
                             tcmod1 in
                         (maybe_restore_opts ();
                          (let uu____1417 =
                             let uu____1418 = FStar_Options.lax () in
                             Prims.op_Negation uu____1418 in
                           if uu____1417
                           then
                             (FStar_SMTEncoding_Encode.encode_modul_from_cache
                                env1 tcmod1 smt_decls;
                              post_smt_encoding ())
                           else ());
                          ((), env1)) in
                   let env1 =
                     FStar_Profiling.profile
                       (fun uu____1424 ->
                          let uu____1425 =
                            with_tcenv_of_env env (extend_tcenv tcmod) in
                          FStar_All.pipe_right uu____1425
                            FStar_Pervasives_Native.snd)
                       FStar_Pervasives_Native.None
                       "FStar.Universal.extend_tcenv" in
                   let mllib =
                     let uu____1437 =
                       ((let uu____1440 = FStar_Options.codegen () in
                         uu____1440 <> FStar_Pervasives_Native.None) &&
                          (let uu____1446 =
                             FStar_Ident.string_of_lid
                               tcmod.FStar_Syntax_Syntax.name in
                           FStar_Options.should_extract uu____1446))
                         &&
                         ((Prims.op_Negation
                             tcmod.FStar_Syntax_Syntax.is_interface)
                            ||
                            (let uu____1448 = FStar_Options.codegen () in
                             uu____1448 =
                               (FStar_Pervasives_Native.Some
                                  FStar_Options.Kremlin))) in
                     if uu____1437
                     then
                       let uu____1455 = maybe_extract_mldefs tcmod env1 in
                       match uu____1455 with
                       | (extracted_defs, _extraction_time) -> extracted_defs
                     else FStar_Pervasives_Native.None in
                   let uu____1471 = maybe_extract_ml_iface tcmod env1 in
                   match uu____1471 with
                   | (env2, _time) -> (tc_result, mllib, env2)))
           else
             (let uu____1489 = tc_source_file () in
              match uu____1489 with
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
          let uu____1548 = tc_one_file env1 pre_fn fn parsing_data in
          match uu____1548 with
          | (tc_result, uu____1562, env2) ->
              let uu____1568 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env2 in
              (tc_result, uu____1568)
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf ->
    fun impl ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1582 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1582 ["fsti"; "fsi"]))
        &&
        (let uu____1584 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1584 ["fst"; "fs"])
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      FStar_Parser_Dep.deps ->
        (Prims.string Prims.list * FStar_CheckedFiles.tc_result *
          FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option *
          uenv))
  =
  fun remaining ->
    fun env ->
      fun deps ->
        let uu____1616 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____1650 =
                let uu____1659 =
                  FStar_All.pipe_right impl
                    (FStar_Parser_Dep.parsing_data_of deps) in
                tc_one_file env (FStar_Pervasives_Native.Some intf) impl
                  uu____1659 in
              (match uu____1650 with
               | (m, mllib, env1) -> (remaining1, (m, mllib, env1)))
          | intf_or_impl::remaining1 ->
              let uu____1697 =
                let uu____1706 =
                  FStar_All.pipe_right intf_or_impl
                    (FStar_Parser_Dep.parsing_data_of deps) in
                tc_one_file env FStar_Pervasives_Native.None intf_or_impl
                  uu____1706 in
              (match uu____1697 with
               | (m, mllib, env1) -> (remaining1, (m, mllib, env1)))
          | [] -> failwith "Impossible: Empty remaining modules" in
        match uu____1616 with
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
        let as_list uu___0_1848 =
          match uu___0_1848 with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some l -> [l] in
        match remaining with
        | [] -> acc
        | uu____1864 ->
            let uu____1867 = acc in
            (match uu____1867 with
             | (mods, mllibs, env) ->
                 let uu____1899 =
                   tc_one_file_from_remaining remaining env deps in
                 (match uu____1899 with
                  | (remaining1, nmod, mllib, env1) ->
                      ((let uu____1935 =
                          let uu____1936 =
                            FStar_Options.profile_group_by_decls () in
                          Prims.op_Negation uu____1936 in
                        if uu____1935
                        then
                          let uu____1937 =
                            FStar_Ident.string_of_lid
                              (nmod.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name in
                          FStar_Profiling.report_and_clear uu____1937
                        else ());
                       tc_fold_interleave deps
                         ((FStar_List.append mods [nmod]),
                           (FStar_List.append mllibs (as_list mllib)), env1)
                         remaining1)))
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      (FStar_CheckedFiles.tc_result Prims.list * uenv * (uenv -> uenv)))
  =
  fun filenames ->
    fun dep_graph ->
      (let uu____1969 =
         FStar_Options.debug_at_level_no_module (FStar_Options.Other "Dep") in
       if uu____1969
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____1972 =
             let uu____1973 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file) in
             FStar_String.concat " " uu____1973 in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____1972))
       else ());
      (let env =
         let uu____1982 = init_env dep_graph in
         FStar_Extraction_ML_UEnv.new_uenv uu____1982 in
       let uu____1983 = tc_fold_interleave dep_graph ([], [], env) filenames in
       match uu____1983 with
       | (all_mods, mllibs, env1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____2027 =
                 with_tcenv_of_env env2
                   (fun tcenv ->
                      (let uu____2036 =
                         (FStar_Options.interactive ()) &&
                           (let uu____2038 = FStar_Errors.get_err_count () in
                            uu____2038 = Prims.int_zero) in
                       if uu____2036
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv)) in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2027 in
             (all_mods, env1, solver_refresh))))