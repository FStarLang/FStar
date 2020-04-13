open Prims
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul -> (Prims.bool * FStar_Ident.lident)) =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
  
type uenv = FStar_Extraction_ML_UEnv.uenv
let with_dsenv_of_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_Syntax_DsEnv.withenv -> ('a * FStar_TypeChecker_Env.env)
  =
  fun tcenv  ->
    fun f  ->
      let uu____39 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____39 with
      | (a1,dsenv) ->
          (a1,
            (let uu___8_51 = tcenv  in
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
               FStar_TypeChecker_Env.use_eq_strict =
                 (uu___8_51.FStar_TypeChecker_Env.use_eq_strict);
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
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___8_51.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___8_51.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (uu___8_51.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (uu___8_51.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___8_51.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___8_51.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv;
               FStar_TypeChecker_Env.nbe =
                 (uu___8_51.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___8_51.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___8_51.FStar_TypeChecker_Env.erasable_types_tab)
             }))
  
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e  ->
    fun f  ->
      let uu____87 =
        let uu____92 = FStar_Extraction_ML_UEnv.tcenv_of_uenv e  in
        f uu____92  in
      match uu____87 with
      | (a1,t') ->
          let uu____99 = FStar_Extraction_ML_UEnv.set_tcenv e t'  in
          (a1, uu____99)
  
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e  ->
    fun f  ->
      let uu____128 =
        let uu____133 = FStar_Extraction_ML_UEnv.tcenv_of_uenv e  in
        with_dsenv_of_tcenv uu____133 f  in
      match uu____128 with
      | (a1,tcenv) ->
          let uu____140 = FStar_Extraction_ML_UEnv.set_tcenv e tcenv  in
          (a1, uu____140)
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____147 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____155 =
             let uu____156 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
             FStar_TypeChecker_Env.push uu____156 "top-level: push_env"  in
           ((), uu____155))
       in
    FStar_Pervasives_Native.snd uu____147
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____164 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____172 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____172))
       in
    FStar_Pervasives_Native.snd uu____164
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____199 = pop_env env1  in res
  
let (env_of_tcenv :
  FStar_TypeChecker_Env.env -> FStar_Extraction_ML_UEnv.uenv) =
  fun env  -> FStar_Extraction_ML_UEnv.new_uenv env 
let (parse :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> (FStar_Syntax_Syntax.modul * uenv))
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____238 = FStar_Parser_Driver.parse_file fn  in
        match uu____238 with
        | (ast,uu____255) ->
            let uu____270 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____283 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____283 with
                   | (pre_ast,uu____300) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____321),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____334 =
                              let uu____339 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____339  in
                            (match uu____334 with
                             | (uu____348,env1) ->
                                 let uu____350 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____350)
                        | uu____356 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____270 with
             | (ast1,env1) ->
                 let uu____373 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____373)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver =
      let uu____385 = FStar_Options.lax ()  in
      if uu____385
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___64_390 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___64_390.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___64_390.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___64_390.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___64_390.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___64_390.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_sig =
             (uu___64_390.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess = FStar_Tactics_Hooks.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___64_390.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___64_390.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___64_390.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____392 =
        let uu____407 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____407  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver
        FStar_Parser_Const.prims_lid uu____392
       in
    let env1 =
      let uu___68_411 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___68_411.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___68_411.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___68_411.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___68_411.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___68_411.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___68_411.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___68_411.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___68_411.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___68_411.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___68_411.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___68_411.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___68_411.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___68_411.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___68_411.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___68_411.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___68_411.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___68_411.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___68_411.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___68_411.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___68_411.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___68_411.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___68_411.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___68_411.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___68_411.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___68_411.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___68_411.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___68_411.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___68_411.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___68_411.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___68_411.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___68_411.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___68_411.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___68_411.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___68_411.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___68_411.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook = FStar_Tactics_Hooks.synthesize;
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___68_411.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice =
          (uu___68_411.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___68_411.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___68_411.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___68_411.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___68_411.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___68_411.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___68_411.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___68_411.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___68_411.FStar_TypeChecker_Env.erasable_types_tab)
      }  in
    let env2 =
      let uu___71_413 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___71_413.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___71_413.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___71_413.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___71_413.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___71_413.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___71_413.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___71_413.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___71_413.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___71_413.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___71_413.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___71_413.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___71_413.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___71_413.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___71_413.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___71_413.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___71_413.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___71_413.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___71_413.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___71_413.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___71_413.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___71_413.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___71_413.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___71_413.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___71_413.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___71_413.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___71_413.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___71_413.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___71_413.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___71_413.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___71_413.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___71_413.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___71_413.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___71_413.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___71_413.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___71_413.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___71_413.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          FStar_Tactics_Hooks.solve_implicits;
        FStar_TypeChecker_Env.splice =
          (uu___71_413.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___71_413.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___71_413.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___71_413.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___71_413.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___71_413.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___71_413.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___71_413.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___71_413.FStar_TypeChecker_Env.erasable_types_tab)
      }  in
    let env3 =
      let uu___74_415 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___74_415.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___74_415.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___74_415.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___74_415.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___74_415.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___74_415.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___74_415.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___74_415.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___74_415.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___74_415.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___74_415.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___74_415.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___74_415.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___74_415.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___74_415.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___74_415.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___74_415.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___74_415.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___74_415.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___74_415.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___74_415.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___74_415.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___74_415.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___74_415.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___74_415.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___74_415.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___74_415.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___74_415.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___74_415.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___74_415.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___74_415.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___74_415.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___74_415.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___74_415.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___74_415.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___74_415.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___74_415.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Hooks.splice;
        FStar_TypeChecker_Env.mpreprocess =
          (uu___74_415.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___74_415.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___74_415.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___74_415.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___74_415.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___74_415.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___74_415.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___74_415.FStar_TypeChecker_Env.erasable_types_tab)
      }  in
    let env4 =
      let uu___77_417 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___77_417.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___77_417.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___77_417.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___77_417.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___77_417.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___77_417.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___77_417.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___77_417.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___77_417.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___77_417.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___77_417.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___77_417.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___77_417.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___77_417.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___77_417.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___77_417.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___77_417.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___77_417.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___77_417.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___77_417.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___77_417.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___77_417.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___77_417.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___77_417.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___77_417.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___77_417.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___77_417.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___77_417.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___77_417.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___77_417.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___77_417.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___77_417.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___77_417.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___77_417.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___77_417.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___77_417.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___77_417.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice =
          (uu___77_417.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess = FStar_Tactics_Hooks.mpreprocess;
        FStar_TypeChecker_Env.postprocess =
          (uu___77_417.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___77_417.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___77_417.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___77_417.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___77_417.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___77_417.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___77_417.FStar_TypeChecker_Env.erasable_types_tab)
      }  in
    let env5 =
      let uu___80_419 = env4  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___80_419.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___80_419.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___80_419.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___80_419.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___80_419.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___80_419.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___80_419.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___80_419.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___80_419.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___80_419.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___80_419.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___80_419.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___80_419.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___80_419.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___80_419.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___80_419.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___80_419.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___80_419.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___80_419.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___80_419.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___80_419.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___80_419.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___80_419.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___80_419.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___80_419.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___80_419.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___80_419.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___80_419.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___80_419.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___80_419.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___80_419.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___80_419.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___80_419.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___80_419.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___80_419.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___80_419.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___80_419.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice =
          (uu___80_419.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___80_419.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess = FStar_Tactics_Hooks.postprocess;
        FStar_TypeChecker_Env.identifier_info =
          (uu___80_419.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___80_419.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___80_419.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___80_419.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___80_419.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___80_419.FStar_TypeChecker_Env.erasable_types_tab)
      }  in
    (env5.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env5; env5
  
let (tc_one_fragment :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env_t ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option *
          FStar_TypeChecker_Env.env))
  =
  fun curmod  ->
    fun env  ->
      fun frag  ->
        let fname env1 =
          let uu____454 = FStar_Options.lsp_server ()  in
          if uu____454
          then
            let uu____458 = FStar_TypeChecker_Env.get_range env1  in
            FStar_Range.file_of_range uu____458
          else
            (let uu____461 = FStar_Options.file_list ()  in
             FStar_List.hd uu____461)
           in
        let acceptable_mod_name modul =
          let uu____473 =
            let uu____475 = fname env  in
            FStar_Parser_Dep.lowercase_module_name uu____475  in
          let uu____477 =
            let uu____479 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____479  in
          uu____473 = uu____477  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____488,{ FStar_Parser_AST.d = uu____489;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.quals = uu____491;
                           FStar_Parser_AST.attrs = uu____492;_}::uu____493)
              -> d
          | FStar_Parser_AST.Interface
              (uu____498,{ FStar_Parser_AST.d = uu____499;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.quals = uu____501;
                           FStar_Parser_AST.attrs = uu____502;_}::uu____503,uu____504)
              -> d
          | uu____511 -> FStar_Range.dummyRange  in
        let uu____512 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____512 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____524 =
              let uu____529 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____529  in
            (match uu____524 with
             | (ast_modul1,env1) ->
                 let uu____550 =
                   let uu____555 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____555
                    in
                 (match uu____550 with
                  | (modul,env2) ->
                      ((let uu____576 =
                          let uu____578 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____578  in
                        if uu____576
                        then
                          let msg =
                            let uu____583 =
                              let uu____585 = fname env2  in
                              FStar_Parser_Dep.module_name_of_file uu____585
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____583
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____591 =
                          let uu____602 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____602
                          then ((modul, []), env2)
                          else
                            (let uu____625 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____625 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____591 with
                        | ((modul1,uu____666),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____689 = FStar_List.hd ast_decls  in
                 (match uu____689 with
                  | { FStar_Parser_AST.d = uu____696;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.quals = uu____698;
                      FStar_Parser_AST.attrs = uu____699;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____709 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____727 =
                            let uu____734 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                modul.FStar_Syntax_Syntax.name a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____734
                             in
                          match uu____727 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____709 with
                  | (env1,ast_decls_l) ->
                      let uu____784 =
                        let uu____791 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____791
                         in
                      (match uu____784 with
                       | (sigelts,env2) ->
                           let uu____823 =
                             let uu____832 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____832
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____823 with
                            | (modul1,uu____854,env3) ->
                                ((FStar_Pervasives_Native.Some modul1), env3)))))
  
let (load_interface_decls :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env_t) =
  fun env  ->
    fun interface_file_name  ->
      let r =
        FStar_Parser_ParseIt.parse
          (FStar_Parser_ParseIt.Filename interface_file_name)
         in
      match r with
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Util.Inl (FStar_Parser_AST.Interface
           (l,decls,uu____878)),uu____879)
          ->
          let uu____902 =
            let uu____907 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____907  in
          FStar_Pervasives_Native.snd uu____902
      | FStar_Parser_ParseIt.ASTFragment uu____919 ->
          let uu____931 =
            let uu____937 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____937)  in
          FStar_Errors.raise_err uu____931
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____947 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
  
let (emit : FStar_Extraction_ML_Syntax.mllib Prims.list -> unit) =
  fun mllibs  ->
    let opt = FStar_Options.codegen ()  in
    if opt <> FStar_Pervasives_Native.None
    then
      let ext =
        match opt with
        | FStar_Pervasives_Native.Some (FStar_Options.FSharp ) -> ".fs"
        | FStar_Pervasives_Native.Some (FStar_Options.OCaml ) -> ".ml"
        | FStar_Pervasives_Native.Some (FStar_Options.Plugin ) -> ".ml"
        | FStar_Pervasives_Native.Some (FStar_Options.Kremlin ) -> ".krml"
        | uu____972 -> failwith "Unrecognized option"  in
      match opt with
      | FStar_Pervasives_Native.Some (FStar_Options.FSharp ) ->
          let outdir = FStar_Options.output_dir ()  in
          FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
            mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.OCaml ) ->
          let outdir = FStar_Options.output_dir ()  in
          FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
            mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.Plugin ) ->
          let outdir = FStar_Options.output_dir ()  in
          FStar_List.iter (FStar_Extraction_ML_PrintML.print outdir ext)
            mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.Kremlin ) ->
          let programs =
            FStar_List.collect FStar_Extraction_Kremlin.translate mllibs  in
          let bin = (FStar_Extraction_Kremlin.current_version, programs)  in
          (match programs with
           | (name,uu____997)::[] ->
               let uu____1000 =
                 FStar_Options.prepend_output_dir (Prims.op_Hat name ext)  in
               FStar_Util.save_value_to_file uu____1000 bin
           | uu____1002 ->
               let uu____1005 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____1005 bin)
      | uu____1008 -> failwith "Unrecognized option"
    else ()
  
let (tc_one_file :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        FStar_Parser_Dep.parsing_data ->
          (FStar_CheckedFiles.tc_result * FStar_Extraction_ML_Syntax.mllib
            FStar_Pervasives_Native.option * uenv))
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        fun parsing_data  ->
          FStar_Ident.reset_gensym ();
          (let maybe_restore_opts uu____1065 =
             let uu____1066 =
               let uu____1068 = FStar_Options.interactive ()  in
               Prims.op_Negation uu____1068  in
             if uu____1066
             then
               let uu____1071 = FStar_Options.restore_cmd_line_options true
                  in
               FStar_All.pipe_right uu____1071 (fun uu____1073  -> ())
             else ()  in
           let post_smt_encoding uu____1081 = FStar_SMTEncoding_Z3.refresh ()
              in
           let maybe_extract_mldefs tcmod env1 =
             let uu____1100 =
               (let uu____1104 = FStar_Options.codegen ()  in
                uu____1104 = FStar_Pervasives_Native.None) ||
                 (let uu____1110 =
                    FStar_Options.should_extract
                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  Prims.op_Negation uu____1110)
                in
             if uu____1100
             then (FStar_Pervasives_Native.None, Prims.int_zero)
             else
               FStar_Util.record_time
                 (fun uu____1129  ->
                    with_env env1
                      (fun env2  ->
                         let uu____1137 =
                           FStar_Extraction_ML_Modul.extract env2 tcmod  in
                         match uu____1137 with | (uu____1146,defs) -> defs))
              in
           let maybe_extract_ml_iface tcmod env1 =
             let uu____1168 =
               let uu____1170 = FStar_Options.codegen ()  in
               uu____1170 = FStar_Pervasives_Native.None  in
             if uu____1168
             then (env1, Prims.int_zero)
             else
               FStar_Util.record_time
                 (fun uu____1189  ->
                    let uu____1190 =
                      with_env env1
                        (fun env2  ->
                           FStar_Extraction_ML_Modul.extract_iface env2 tcmod)
                       in
                    match uu____1190 with | (env2,uu____1202) -> env2)
              in
           let tc_source_file uu____1216 =
             let uu____1217 = parse env pre_fn fn  in
             match uu____1217 with
             | (fmod,env1) ->
                 let mii =
                   let uu____1233 =
                     let uu____1234 =
                       FStar_Extraction_ML_UEnv.tcenv_of_uenv env1  in
                     uu____1234.FStar_TypeChecker_Env.dsenv  in
                   FStar_Syntax_DsEnv.inclusion_info uu____1233
                     fmod.FStar_Syntax_Syntax.name
                    in
                 let check_mod uu____1248 =
                   let check env2 =
                     with_tcenv_of_env env2
                       (fun tcenv  ->
                          (match tcenv.FStar_TypeChecker_Env.gamma with
                           | [] -> ()
                           | uu____1288 ->
                               failwith
                                 "Impossible: gamma contains leaked names");
                          (let uu____1292 =
                             FStar_TypeChecker_Tc.check_module tcenv fmod
                               (FStar_Util.is_some pre_fn)
                              in
                           match uu____1292 with
                           | (modul,env3) ->
                               (maybe_restore_opts ();
                                (let smt_decls =
                                   let uu____1322 =
                                     let uu____1324 = FStar_Options.lax ()
                                        in
                                     Prims.op_Negation uu____1324  in
                                   if uu____1322
                                   then
                                     let smt_decls =
                                       FStar_SMTEncoding_Encode.encode_modul
                                         env3 modul
                                        in
                                     (post_smt_encoding (); smt_decls)
                                   else ([], [])  in
                                 ((modul, smt_decls), env3)))))
                      in
                   let uu____1361 =
                     FStar_Profiling.profile (fun uu____1391  -> check env1)
                       (FStar_Pervasives_Native.Some
                          ((fmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                       "FStar.Universal.tc_source_file"
                      in
                   match uu____1361 with
                   | ((tcmod,smt_decls),env2) ->
                       let tc_time = Prims.int_zero  in
                       let uu____1430 = maybe_extract_mldefs tcmod env2  in
                       (match uu____1430 with
                        | (extracted_defs,extract_time) ->
                            let uu____1454 =
                              maybe_extract_ml_iface tcmod env2  in
                            (match uu____1454 with
                             | (env3,iface_extraction_time) ->
                                 ({
                                    FStar_CheckedFiles.checked_module = tcmod;
                                    FStar_CheckedFiles.mii = mii;
                                    FStar_CheckedFiles.smt_decls = smt_decls;
                                    FStar_CheckedFiles.tc_time = tc_time;
                                    FStar_CheckedFiles.extraction_time =
                                      (extract_time + iface_extraction_time)
                                  }, extracted_defs, env3)))
                    in
                 let uu____1474 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                    in
                 if uu____1474
                 then
                   let uu____1485 = FStar_Parser_ParseIt.find_file fn  in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1485
                     check_mod
                 else check_mod ()
              in
           let uu____1497 =
             let uu____1499 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____1499  in
           if uu____1497
           then
             let uu____1510 =
               FStar_CheckedFiles.load_module_from_cache env fn  in
             match uu____1510 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____1522 =
                     let uu____1524 = FStar_Parser_Dep.module_name_of_file fn
                        in
                     FStar_Options.should_be_already_cached uu____1524  in
                   if uu____1522
                   then
                     let uu____1527 =
                       let uu____1533 =
                         FStar_Util.format1
                           "Expected %s to already be checked" fn
                          in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____1533)
                        in
                     FStar_Errors.raise_err uu____1527
                   else ());
                  (let uu____1540 =
                     (let uu____1544 = FStar_Options.codegen ()  in
                      FStar_Option.isSome uu____1544) &&
                       (FStar_Options.cmi ())
                      in
                   if uu____1540
                   then
                     let uu____1548 =
                       let uu____1554 =
                         FStar_Util.format1
                           "Cross-module inlining expects all modules to be checked first; %s was not checked"
                           fn
                          in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____1554)
                        in
                     FStar_Errors.raise_err uu____1548
                   else ());
                  (let uu____1560 = tc_source_file ()  in
                   match uu____1560 with
                   | (tc_result,mllib,env1) ->
                       ((let uu____1585 =
                           (let uu____1589 = FStar_Errors.get_err_count ()
                               in
                            uu____1589 = Prims.int_zero) &&
                             ((FStar_Options.lax ()) ||
                                (FStar_Options.should_verify
                                   ((tc_result.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                            in
                         if uu____1585
                         then
                           FStar_CheckedFiles.store_module_to_cache env1 fn
                             parsing_data tc_result
                         else ());
                        (tc_result, mllib, env1))))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.FStar_CheckedFiles.checked_module  in
                 let smt_decls = tc_result.FStar_CheckedFiles.smt_decls  in
                 ((let uu____1608 =
                     FStar_Options.dump_module
                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____1608
                   then
                     let uu____1611 =
                       FStar_Syntax_Print.modul_to_string tcmod  in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____1611
                   else ());
                  (let extend_tcenv tcmod1 tcenv =
                     let uu____1631 =
                       let uu____1636 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                           tc_result.FStar_CheckedFiles.mii
                           (FStar_TypeChecker_Normalize.erase_universes tcenv)
                          in
                       FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                         uu____1636
                        in
                     match uu____1631 with
                     | (uu____1652,tcenv1) ->
                         let env1 =
                           FStar_TypeChecker_Tc.load_checked_module tcenv1
                             tcmod1
                            in
                         (maybe_restore_opts ();
                          (let uu____1657 =
                             let uu____1659 = FStar_Options.lax ()  in
                             Prims.op_Negation uu____1659  in
                           if uu____1657
                           then
                             (FStar_SMTEncoding_Encode.encode_modul_from_cache
                                env1 tcmod1 smt_decls;
                              post_smt_encoding ())
                           else ());
                          ((), env1))
                      in
                   let env1 =
                     FStar_Profiling.profile
                       (fun uu____1668  ->
                          let uu____1669 =
                            with_tcenv_of_env env (extend_tcenv tcmod)  in
                          FStar_All.pipe_right uu____1669
                            FStar_Pervasives_Native.snd)
                       FStar_Pervasives_Native.None
                       "FStar.Universal.extend_tcenv"
                      in
                   let mllib =
                     let uu____1683 =
                       ((let uu____1687 = FStar_Options.codegen ()  in
                         uu____1687 <> FStar_Pervasives_Native.None) &&
                          (FStar_Options.should_extract
                             (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                         &&
                         ((Prims.op_Negation
                             tcmod.FStar_Syntax_Syntax.is_interface)
                            ||
                            (let uu____1693 = FStar_Options.codegen ()  in
                             uu____1693 =
                               (FStar_Pervasives_Native.Some
                                  FStar_Options.Kremlin)))
                        in
                     if uu____1683
                     then
                       let uu____1701 = maybe_extract_mldefs tcmod env1  in
                       match uu____1701 with
                       | (extracted_defs,_extraction_time) -> extracted_defs
                     else FStar_Pervasives_Native.None  in
                   let uu____1721 = maybe_extract_ml_iface tcmod env1  in
                   match uu____1721 with
                   | (env2,_time) -> (tc_result, mllib, env2)))
           else
             (let uu____1743 = tc_source_file ()  in
              match uu____1743 with
              | (tc_result,mllib,env1) -> (tc_result, mllib, env1)))
  
let (tc_one_file_for_ide :
  FStar_TypeChecker_Env.env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        FStar_Parser_Dep.parsing_data ->
          (FStar_CheckedFiles.tc_result * FStar_TypeChecker_Env.env_t))
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        fun parsing_data  ->
          let env1 = env_of_tcenv env  in
          let uu____1807 = tc_one_file env1 pre_fn fn parsing_data  in
          match uu____1807 with
          | (tc_result,uu____1821,env2) ->
              let uu____1827 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env2
                 in
              (tc_result, uu____1827)
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____1850 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____1850 ["fsti"; "fsi"]))
        &&
        (let uu____1859 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____1859 ["fst"; "fs"])
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      FStar_Parser_Dep.deps ->
        (Prims.string Prims.list * FStar_CheckedFiles.tc_result *
          FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option *
          uenv))
  =
  fun remaining  ->
    fun env  ->
      fun deps  ->
        let uu____1902 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____1943 =
                let uu____1952 =
                  FStar_All.pipe_right impl
                    (FStar_Parser_Dep.parsing_data_of deps)
                   in
                tc_one_file env (FStar_Pervasives_Native.Some intf) impl
                  uu____1952
                 in
              (match uu____1943 with
               | (m,mllib,env1) -> (remaining1, (m, mllib, env1)))
          | intf_or_impl::remaining1 ->
              let uu____1997 =
                let uu____2006 =
                  FStar_All.pipe_right intf_or_impl
                    (FStar_Parser_Dep.parsing_data_of deps)
                   in
                tc_one_file env FStar_Pervasives_Native.None intf_or_impl
                  uu____2006
                 in
              (match uu____1997 with
               | (m,mllib,env1) -> (remaining1, (m, mllib, env1)))
          | [] -> failwith "Impossible: Empty remaining modules"  in
        match uu____1902 with
        | (remaining1,(nmods,mllib,env1)) -> (remaining1, nmods, mllib, env1)
  
let rec (tc_fold_interleave :
  FStar_Parser_Dep.deps ->
    (FStar_CheckedFiles.tc_result Prims.list *
      FStar_Extraction_ML_Syntax.mllib Prims.list * uenv) ->
      Prims.string Prims.list ->
        (FStar_CheckedFiles.tc_result Prims.list *
          FStar_Extraction_ML_Syntax.mllib Prims.list * uenv))
  =
  fun deps  ->
    fun acc  ->
      fun remaining  ->
        let as_list uu___0_2162 =
          match uu___0_2162 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some l -> [l]  in
        match remaining with
        | [] -> acc
        | uu____2179 ->
            let uu____2183 = acc  in
            (match uu____2183 with
             | (mods,mllibs,env) ->
                 let uu____2215 =
                   tc_one_file_from_remaining remaining env deps  in
                 (match uu____2215 with
                  | (remaining1,nmod,mllib,env1) ->
                      ((let uu____2254 =
                          let uu____2256 =
                            FStar_Options.profile_group_by_decls ()  in
                          Prims.op_Negation uu____2256  in
                        if uu____2254
                        then
                          let uu____2259 =
                            FStar_Ident.string_of_lid
                              (nmod.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name
                             in
                          FStar_Profiling.report_and_clear uu____2259
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
  fun filenames  ->
    fun dep_graph  ->
      (let uu____2296 =
         FStar_Options.debug_at_level_no_module (FStar_Options.Other "Dep")
          in
       if uu____2296
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____2305 =
             let uu____2307 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____2307  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____2305))
       else ());
      (let env =
         let uu____2323 = init_env dep_graph  in
         FStar_Extraction_ML_UEnv.new_uenv uu____2323  in
       let uu____2324 = tc_fold_interleave dep_graph ([], [], env) filenames
          in
       match uu____2324 with
       | (all_mods,mllibs,env1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____2368 =
                 with_tcenv_of_env env2
                   (fun tcenv  ->
                      (let uu____2377 =
                         (FStar_Options.interactive ()) &&
                           (let uu____2380 = FStar_Errors.get_err_count ()
                               in
                            uu____2380 = Prims.int_zero)
                          in
                       if uu____2377
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv))
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2368  in
             (all_mods, env1, solver_refresh))))
  