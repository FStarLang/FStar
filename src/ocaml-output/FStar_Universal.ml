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
      let uu____71177 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____71177 with
      | (a,dsenv1) ->
          (a,
            (let uu___703_71189 = tcenv  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___703_71189.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___703_71189.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___703_71189.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___703_71189.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___703_71189.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___703_71189.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___703_71189.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___703_71189.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___703_71189.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___703_71189.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___703_71189.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___703_71189.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___703_71189.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___703_71189.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___703_71189.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___703_71189.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___703_71189.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___703_71189.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___703_71189.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___703_71189.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___703_71189.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___703_71189.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___703_71189.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___703_71189.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___703_71189.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___703_71189.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___703_71189.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___703_71189.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___703_71189.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___703_71189.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___703_71189.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___703_71189.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___703_71189.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___703_71189.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___703_71189.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___703_71189.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___703_71189.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___703_71189.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___703_71189.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___703_71189.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___703_71189.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___703_71189.FStar_TypeChecker_Env.nbe)
             }))
  
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e  ->
    fun f  ->
      let uu____71225 = f e.FStar_Extraction_ML_UEnv.env_tcenv  in
      match uu____71225 with
      | (a,t') ->
          (a,
            (let uu___711_71237 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___711_71237.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___711_71237.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___711_71237.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___711_71237.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e  ->
    fun f  ->
      let uu____71266 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f  in
      match uu____71266 with
      | (a,tcenv) ->
          (a,
            (let uu___719_71278 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___719_71278.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___719_71278.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___719_71278.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___719_71278.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____71285 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____71293 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env"
              in
           ((), uu____71293))
       in
    FStar_Pervasives_Native.snd uu____71285
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____71301 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____71309 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____71309))
       in
    FStar_Pervasives_Native.snd uu____71301
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____71336 = pop_env env1  in res
  
let (env_of_tcenv :
  FStar_TypeChecker_Env.env -> FStar_Extraction_ML_UEnv.uenv) =
  fun env  -> FStar_Extraction_ML_UEnv.mkContext env 
let (parse :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> (FStar_Syntax_Syntax.modul * uenv))
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____71375 = FStar_Parser_Driver.parse_file fn  in
        match uu____71375 with
        | (ast,uu____71392) ->
            let uu____71407 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____71420 = FStar_Parser_Driver.parse_file pre_fn1
                     in
                  (match uu____71420 with
                   | (pre_ast,uu____71437) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____71458),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____71471 =
                              let uu____71476 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____71476  in
                            (match uu____71471 with
                             | (uu____71485,env1) ->
                                 let uu____71487 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____71487)
                        | uu____71493 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____71407 with
             | (ast1,env1) ->
                 let uu____71510 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____71510)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____71522 = FStar_Options.lax ()  in
      if uu____71522
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___763_71527 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___763_71527.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___763_71527.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___763_71527.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___763_71527.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___763_71527.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_sig =
             (uu___763_71527.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___763_71527.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___763_71527.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___763_71527.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____71529 =
        let uu____71544 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____71544  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____71529
       in
    let env1 =
      let uu___767_71548 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___767_71548.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___767_71548.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___767_71548.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___767_71548.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___767_71548.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___767_71548.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___767_71548.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___767_71548.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___767_71548.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___767_71548.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___767_71548.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___767_71548.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___767_71548.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___767_71548.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___767_71548.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___767_71548.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___767_71548.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___767_71548.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___767_71548.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___767_71548.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___767_71548.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___767_71548.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___767_71548.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___767_71548.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___767_71548.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___767_71548.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___767_71548.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___767_71548.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___767_71548.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___767_71548.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___767_71548.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___767_71548.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___767_71548.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___767_71548.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___767_71548.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___767_71548.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___767_71548.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___767_71548.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___767_71548.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___767_71548.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___767_71548.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___767_71548.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___770_71550 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___770_71550.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___770_71550.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___770_71550.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___770_71550.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___770_71550.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___770_71550.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___770_71550.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___770_71550.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___770_71550.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___770_71550.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___770_71550.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___770_71550.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___770_71550.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___770_71550.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___770_71550.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___770_71550.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___770_71550.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___770_71550.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___770_71550.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___770_71550.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___770_71550.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___770_71550.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___770_71550.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___770_71550.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___770_71550.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___770_71550.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___770_71550.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___770_71550.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___770_71550.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___770_71550.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___770_71550.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___770_71550.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___770_71550.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___770_71550.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___770_71550.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___770_71550.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___770_71550.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___770_71550.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___770_71550.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___770_71550.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___770_71550.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___770_71550.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___773_71552 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___773_71552.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___773_71552.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___773_71552.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___773_71552.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___773_71552.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___773_71552.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___773_71552.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___773_71552.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___773_71552.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___773_71552.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___773_71552.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___773_71552.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___773_71552.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___773_71552.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___773_71552.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___773_71552.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___773_71552.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___773_71552.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___773_71552.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___773_71552.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___773_71552.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___773_71552.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___773_71552.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___773_71552.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___773_71552.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___773_71552.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___773_71552.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___773_71552.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___773_71552.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___773_71552.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___773_71552.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___773_71552.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___773_71552.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___773_71552.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___773_71552.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___773_71552.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___773_71552.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___773_71552.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___773_71552.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___773_71552.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___773_71552.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___773_71552.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___776_71554 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___776_71554.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___776_71554.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___776_71554.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___776_71554.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___776_71554.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___776_71554.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___776_71554.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___776_71554.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___776_71554.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___776_71554.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___776_71554.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___776_71554.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___776_71554.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___776_71554.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___776_71554.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___776_71554.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___776_71554.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___776_71554.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___776_71554.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___776_71554.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___776_71554.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___776_71554.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___776_71554.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___776_71554.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___776_71554.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___776_71554.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___776_71554.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___776_71554.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___776_71554.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___776_71554.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___776_71554.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___776_71554.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___776_71554.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___776_71554.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___776_71554.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___776_71554.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___776_71554.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___776_71554.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___776_71554.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___776_71554.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___776_71554.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___776_71554.FStar_TypeChecker_Env.nbe)
      }  in
    (env4.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env4; env4
  
let (tc_one_fragment :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env_t ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option *
          FStar_TypeChecker_Env.env_t))
  =
  fun curmod  ->
    fun env  ->
      fun frag  ->
        let acceptable_mod_name modul =
          let uu____71589 =
            let uu____71591 =
              let uu____71593 = FStar_Options.file_list ()  in
              FStar_List.hd uu____71593  in
            FStar_Parser_Dep.lowercase_module_name uu____71591  in
          let uu____71598 =
            let uu____71600 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____71600  in
          uu____71589 = uu____71598  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____71609,{ FStar_Parser_AST.d = uu____71610;
                             FStar_Parser_AST.drange = d;
                             FStar_Parser_AST.doc = uu____71612;
                             FStar_Parser_AST.quals = uu____71613;
                             FStar_Parser_AST.attrs = uu____71614;_}::uu____71615)
              -> d
          | FStar_Parser_AST.Interface
              (uu____71622,{ FStar_Parser_AST.d = uu____71623;
                             FStar_Parser_AST.drange = d;
                             FStar_Parser_AST.doc = uu____71625;
                             FStar_Parser_AST.quals = uu____71626;
                             FStar_Parser_AST.attrs = uu____71627;_}::uu____71628,uu____71629)
              -> d
          | uu____71638 -> FStar_Range.dummyRange  in
        let uu____71639 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____71639 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____71651 =
              let uu____71656 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____71656  in
            (match uu____71651 with
             | (ast_modul1,env1) ->
                 let uu____71677 =
                   let uu____71682 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____71682
                    in
                 (match uu____71677 with
                  | (modul,env2) ->
                      ((let uu____71703 =
                          let uu____71705 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____71705  in
                        if uu____71703
                        then
                          let msg =
                            let uu____71710 =
                              let uu____71712 =
                                let uu____71714 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____71714  in
                              FStar_Parser_Dep.module_name_of_file
                                uu____71712
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____71710
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____71723 =
                          let uu____71734 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____71734
                          then ((modul, []), env2)
                          else
                            (let uu____71757 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____71757 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____71723 with
                        | ((modul1,uu____71798),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____71821 = FStar_List.hd ast_decls  in
                 (match uu____71821 with
                  | { FStar_Parser_AST.d = uu____71828;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____71830;
                      FStar_Parser_AST.quals = uu____71831;
                      FStar_Parser_AST.attrs = uu____71832;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____71844 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____71862 =
                            let uu____71869 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____71869
                             in
                          match uu____71862 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____71844 with
                  | (env1,ast_decls_l) ->
                      let uu____71919 =
                        let uu____71924 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____71924
                         in
                      (match uu____71919 with
                       | (sigelts,env2) ->
                           let uu____71944 =
                             let uu____71953 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____71953
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____71944 with
                            | (modul1,uu____71975,env3) ->
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
           (l,decls,uu____71999)),uu____72000)
          ->
          let uu____72023 =
            let uu____72028 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____72028  in
          FStar_Pervasives_Native.snd uu____72023
      | FStar_Parser_ParseIt.ASTFragment uu____72040 ->
          let uu____72052 =
            let uu____72058 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____72058)  in
          FStar_Errors.raise_err uu____72052
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____72068 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
  
type delta_env = (uenv -> uenv) FStar_Pervasives_Native.option
let (apply_delta_env : uenv -> delta_env -> uenv) =
  fun env  ->
    fun f  ->
      match f with
      | FStar_Pervasives_Native.None  -> env
      | FStar_Pervasives_Native.Some f1 -> f1 env
  
let (extend_delta_env :
  delta_env ->
    (uenv -> uenv) -> (uenv -> uenv) FStar_Pervasives_Native.option)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some g
      | FStar_Pervasives_Native.Some f1 ->
          FStar_Pervasives_Native.Some
            ((fun e  -> let uu____72141 = f1 e  in g uu____72141))
  
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
        | uu____72165 -> failwith "Unrecognized option"  in
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
           | (name,uu____72190)::[] ->
               let uu____72193 =
                 FStar_Options.prepend_output_dir (Prims.op_Hat name ext)  in
               FStar_Util.save_value_to_file uu____72193 bin
           | uu____72195 ->
               let uu____72198 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____72198 bin)
      | uu____72201 -> failwith "Unrecognized option"
    else ()
  
let (tc_one_file :
  uenv ->
    delta_env ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          FStar_Parser_Dep.parsing_data ->
            (FStar_CheckedFiles.tc_result * FStar_Extraction_ML_Syntax.mllib
              FStar_Pervasives_Native.option * uenv * delta_env))
  =
  fun env  ->
    fun delta1  ->
      fun pre_fn  ->
        fun fn  ->
          fun parsing_data  ->
            FStar_Ident.reset_gensym ();
            (let post_smt_encoding uu____72267 =
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____72269 =
                  let uu____72271 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____72271  in
                if uu____72269
                then
                  let uu____72274 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____72274 (fun a1  -> ())
                else ())
                in
             let maybe_extract_mldefs tcmod env1 =
               let uu____72296 =
                 (let uu____72300 = FStar_Options.codegen ()  in
                  uu____72300 = FStar_Pervasives_Native.None) ||
                   (let uu____72306 =
                      FStar_Options.should_extract
                        (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    Prims.op_Negation uu____72306)
                  in
               if uu____72296
               then (FStar_Pervasives_Native.None, (Prims.parse_int "0"))
               else
                 FStar_Util.record_time
                   (fun uu____72328  ->
                      let uu____72329 =
                        FStar_Extraction_ML_Modul.extract env1 tcmod  in
                      match uu____72329 with | (uu____72338,defs) -> defs)
                in
             let maybe_extract_ml_iface tcmod env1 =
               let uu____72360 =
                 let uu____72362 = FStar_Options.codegen ()  in
                 uu____72362 = FStar_Pervasives_Native.None  in
               if uu____72360
               then (env1, (Prims.parse_int "0"))
               else
                 (let uu____72377 =
                    FStar_Util.record_time
                      (fun uu____72392  ->
                         FStar_Extraction_ML_Modul.extract_iface env1 tcmod)
                     in
                  match uu____72377 with
                  | ((env2,_extracted_iface),iface_extract_time) ->
                      (env2, iface_extract_time))
                in
             let tc_source_file uu____72421 =
               let env1 = apply_delta_env env delta1  in
               let uu____72423 = parse env1 pre_fn fn  in
               match uu____72423 with
               | (fmod,env2) ->
                   let mii =
                     FStar_Syntax_DsEnv.inclusion_info
                       (env2.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                       fmod.FStar_Syntax_Syntax.name
                      in
                   let check_mod uu____72452 =
                     let uu____72453 =
                       FStar_Util.record_time
                         (fun uu____72488  ->
                            with_tcenv_of_env env2
                              (fun tcenv  ->
                                 (match tcenv.FStar_TypeChecker_Env.gamma
                                  with
                                  | [] -> ()
                                  | uu____72507 ->
                                      failwith
                                        "Impossible: gamma contains leaked names");
                                 (let uu____72511 =
                                    FStar_TypeChecker_Tc.check_module tcenv
                                      fmod (FStar_Util.is_some pre_fn)
                                     in
                                  match uu____72511 with
                                  | (modul,env3) ->
                                      let smt_decls =
                                        let uu____72540 =
                                          let uu____72542 =
                                            FStar_Options.lax ()  in
                                          Prims.op_Negation uu____72542  in
                                        if uu____72540
                                        then
                                          let smt_decls =
                                            FStar_SMTEncoding_Encode.encode_modul
                                              env3 modul
                                             in
                                          (post_smt_encoding (); smt_decls)
                                        else ([], [])  in
                                      ((modul, smt_decls), env3))))
                        in
                     match uu____72453 with
                     | (((tcmod,smt_decls),env3),tc_time) ->
                         let uu____72629 =
                           with_env env3 (maybe_extract_mldefs tcmod)  in
                         (match uu____72629 with
                          | (extracted_defs,extract_time) ->
                              let uu____72660 =
                                with_env env3 (maybe_extract_ml_iface tcmod)
                                 in
                              (match uu____72660 with
                               | (env4,iface_extraction_time) ->
                                   ({
                                      FStar_CheckedFiles.checked_module =
                                        tcmod;
                                      FStar_CheckedFiles.mii = mii;
                                      FStar_CheckedFiles.smt_decls =
                                        smt_decls;
                                      FStar_CheckedFiles.tc_time = tc_time;
                                      FStar_CheckedFiles.extraction_time =
                                        (extract_time + iface_extraction_time)
                                    }, extracted_defs, env4)))
                      in
                   let uu____72685 =
                     (FStar_Options.should_verify
                        (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                       &&
                       ((FStar_Options.record_hints ()) ||
                          (FStar_Options.use_hints ()))
                      in
                   if uu____72685
                   then
                     let uu____72696 = FStar_Parser_ParseIt.find_file fn  in
                     FStar_SMTEncoding_Solver.with_hints_db uu____72696
                       check_mod
                   else check_mod ()
                in
             let uu____72708 =
               let uu____72710 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____72710  in
             if uu____72708
             then
               let uu____72723 =
                 FStar_CheckedFiles.load_module_from_cache env fn  in
               match uu____72723 with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____72737 =
                       let uu____72739 =
                         FStar_Parser_Dep.module_name_of_file fn  in
                       FStar_Options.should_be_already_cached uu____72739  in
                     if uu____72737
                     then
                       let uu____72742 =
                         let uu____72748 =
                           FStar_Util.format1
                             "Expected %s to already be checked" fn
                            in
                         (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                           uu____72748)
                          in
                       FStar_Errors.raise_err uu____72742
                     else ());
                    (let uu____72755 =
                       (let uu____72759 = FStar_Options.codegen ()  in
                        FStar_Option.isSome uu____72759) &&
                         (FStar_Options.cmi ())
                        in
                     if uu____72755
                     then
                       let uu____72763 =
                         let uu____72769 =
                           FStar_Util.format1
                             "Cross-module inlining expects all modules to be checked first; %s was not checked"
                             fn
                            in
                         (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                           uu____72769)
                          in
                       FStar_Errors.raise_err uu____72763
                     else ());
                    (let uu____72775 = tc_source_file ()  in
                     match uu____72775 with
                     | (tc_result,mllib,env1) ->
                         ((let uu____72802 =
                             (let uu____72806 = FStar_Errors.get_err_count ()
                                 in
                              uu____72806 = (Prims.parse_int "0")) &&
                               ((FStar_Options.lax ()) ||
                                  (FStar_Options.should_verify
                                     ((tc_result.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                              in
                           if uu____72802
                           then
                             FStar_CheckedFiles.store_module_to_cache env1 fn
                               parsing_data tc_result
                           else ());
                          (tc_result, mllib, env1,
                            FStar_Pervasives_Native.None))))
               | FStar_Pervasives_Native.Some tc_result ->
                   let tcmod = tc_result.FStar_CheckedFiles.checked_module
                      in
                   let smt_decls = tc_result.FStar_CheckedFiles.smt_decls  in
                   ((let uu____72828 =
                       FStar_Options.dump_module
                         (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                        in
                     if uu____72828
                     then
                       let uu____72831 =
                         FStar_Syntax_Print.modul_to_string tcmod  in
                       FStar_Util.print1 "Module after type checking:\n%s\n"
                         uu____72831
                     else ());
                    (let delta_tcenv tcmod1 tcenv =
                       let uu____72851 =
                         let uu____72856 =
                           FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                             tc_result.FStar_CheckedFiles.mii
                             (FStar_TypeChecker_Normalize.erase_universes
                                tcenv)
                            in
                         FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                           uu____72856
                          in
                       match uu____72851 with
                       | (uu____72872,tcenv1) ->
                           let env1 =
                             FStar_TypeChecker_Tc.load_checked_module tcenv1
                               tcmod1
                              in
                           ((let uu____72876 =
                               let uu____72878 = FStar_Options.lax ()  in
                               Prims.op_Negation uu____72878  in
                             if uu____72876
                             then
                               (FStar_SMTEncoding_Encode.encode_modul_from_cache
                                  env1 tcmod1.FStar_Syntax_Syntax.name
                                  smt_decls;
                                post_smt_encoding ())
                             else ());
                            ((), env1))
                        in
                     let mllib =
                       let uu____72887 =
                         ((let uu____72891 = FStar_Options.codegen ()  in
                           uu____72891 <> FStar_Pervasives_Native.None) &&
                            (FStar_Options.should_extract
                               (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                           &&
                           ((Prims.op_Negation
                               tcmod.FStar_Syntax_Syntax.is_interface)
                              ||
                              (let uu____72897 = FStar_Options.codegen ()  in
                               uu____72897 =
                                 (FStar_Pervasives_Native.Some
                                    FStar_Options.Kremlin)))
                          in
                       if uu____72887
                       then
                         with_env env
                           (fun env1  ->
                              let env2 = apply_delta_env env1 delta1  in
                              let extract_defs tcmod1 env3 =
                                let uu____72933 =
                                  with_tcenv_of_env env3 (delta_tcenv tcmod1)
                                   in
                                match uu____72933 with
                                | (uu____72945,env4) ->
                                    maybe_extract_mldefs tcmod1 env4
                                 in
                              let uu____72947 = extract_defs tcmod env2  in
                              match uu____72947 with
                              | (extracted_defs,extraction_time) ->
                                  extracted_defs)
                       else FStar_Pervasives_Native.None  in
                     let delta_env env1 =
                       FStar_Options.profile
                         (fun uu____72980  ->
                            let uu____72981 =
                              with_tcenv_of_env env1 (delta_tcenv tcmod)  in
                            match uu____72981 with
                            | (uu____72986,env2) ->
                                let uu____72988 =
                                  with_env env2
                                    (maybe_extract_ml_iface tcmod)
                                   in
                                (match uu____72988 with
                                 | (env3,_time) -> env3))
                         (fun uu____73004  ->
                            FStar_Util.format1
                              "Extending environment with module %s"
                              (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                        in
                     (tc_result, mllib, env,
                       (extend_delta_env delta1 delta_env))))
             else
               (let uu____73010 = tc_source_file ()  in
                match uu____73010 with
                | (tc_result,mllib,env1) ->
                    (tc_result, mllib, env1, FStar_Pervasives_Native.None)))
  
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
          let uu____73079 =
            tc_one_file env1 FStar_Pervasives_Native.None pre_fn fn
              parsing_data
             in
          match uu____73079 with
          | (tc_result,uu____73098,env2,delta1) ->
              let uu____73105 =
                let uu____73106 = apply_delta_env env2 delta1  in
                uu____73106.FStar_Extraction_ML_UEnv.env_tcenv  in
              (tc_result, uu____73105)
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____73129 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____73129 ["fsti"; "fsi"]))
        &&
        (let uu____73138 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____73138 ["fst"; "fs"])
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      delta_env ->
        FStar_Parser_Dep.deps ->
          (Prims.string Prims.list * FStar_CheckedFiles.tc_result Prims.list
            * FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option
            * uenv * delta_env))
  =
  fun remaining  ->
    fun env  ->
      fun delta_env  ->
        fun deps  ->
          let uu____73190 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____73239 =
                  let uu____73250 =
                    FStar_All.pipe_right impl
                      (FStar_Parser_Dep.parsing_data_of deps)
                     in
                  tc_one_file env delta_env
                    (FStar_Pervasives_Native.Some intf) impl uu____73250
                   in
                (match uu____73239 with
                 | (m,mllib,env1,delta_env1) ->
                     (remaining1, ([m], mllib, env1, delta_env1)))
            | intf_or_impl::remaining1 ->
                let uu____73306 =
                  let uu____73317 =
                    FStar_All.pipe_right intf_or_impl
                      (FStar_Parser_Dep.parsing_data_of deps)
                     in
                  tc_one_file env delta_env FStar_Pervasives_Native.None
                    intf_or_impl uu____73317
                   in
                (match uu____73306 with
                 | (m,mllib,env1,delta_env1) ->
                     (remaining1, ([m], mllib, env1, delta_env1)))
            | [] -> ([], ([], FStar_Pervasives_Native.None, env, delta_env))
             in
          match uu____73190 with
          | (remaining1,(nmods,mllib,env1,delta_env1)) ->
              (remaining1, nmods, mllib, env1, delta_env1)
  
let rec (tc_fold_interleave :
  FStar_Parser_Dep.deps ->
    (FStar_CheckedFiles.tc_result Prims.list *
      FStar_Extraction_ML_Syntax.mllib Prims.list * uenv * delta_env) ->
      Prims.string Prims.list ->
        (FStar_CheckedFiles.tc_result Prims.list *
          FStar_Extraction_ML_Syntax.mllib Prims.list * uenv * delta_env))
  =
  fun deps  ->
    fun acc  ->
      fun remaining  ->
        let as_list uu___695_73509 =
          match uu___695_73509 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some l -> [l]  in
        match remaining with
        | [] -> acc
        | uu____73528 ->
            let uu____73532 = acc  in
            (match uu____73532 with
             | (mods,mllibs,env,delta_env) ->
                 let uu____73569 =
                   tc_one_file_from_remaining remaining env delta_env deps
                    in
                 (match uu____73569 with
                  | (remaining1,nmods,mllib,env1,delta_env1) ->
                      tc_fold_interleave deps
                        ((FStar_List.append mods nmods),
                          (FStar_List.append mllibs (as_list mllib)), env1,
                          delta_env1) remaining1))
  
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      (FStar_CheckedFiles.tc_result Prims.list * uenv * (uenv -> uenv)
        FStar_Pervasives_Native.option))
  =
  fun filenames  ->
    fun dep_graph1  ->
      (let uu____73653 = FStar_Options.debug_any ()  in
       if uu____73653
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____73661 =
             let uu____73663 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____73663  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____73661))
       else ());
      (let env =
         let uu____73679 = init_env dep_graph1  in
         FStar_Extraction_ML_UEnv.mkContext uu____73679  in
       let uu____73680 =
         tc_fold_interleave dep_graph1
           ([], [], env, FStar_Pervasives_Native.None) filenames
          in
       match uu____73680 with
       | (all_mods,mllibs,env1,delta1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____73732 =
                 with_tcenv_of_env env2
                   (fun tcenv  ->
                      (let uu____73741 =
                         (FStar_Options.interactive ()) &&
                           (let uu____73744 = FStar_Errors.get_err_count ()
                               in
                            uu____73744 = (Prims.parse_int "0"))
                          in
                       if uu____73741
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv))
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____73732
                in
             (all_mods, env1, (extend_delta_env delta1 solver_refresh)))))
  