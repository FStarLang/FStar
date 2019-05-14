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
      let uu____284 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____284 with
      | (a,dsenv1) ->
          (a,
            (let uu___8_404 = tcenv  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___8_404.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___8_404.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___8_404.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___8_404.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___8_404.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___8_404.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___8_404.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___8_404.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___8_404.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___8_404.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___8_404.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___8_404.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___8_404.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___8_404.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___8_404.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___8_404.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___8_404.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___8_404.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___8_404.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___8_404.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___8_404.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___8_404.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___8_404.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___8_404.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___8_404.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___8_404.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___8_404.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___8_404.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___8_404.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___8_404.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___8_404.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___8_404.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___8_404.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___8_404.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___8_404.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___8_404.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___8_404.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___8_404.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___8_404.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___8_404.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___8_404.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___8_404.FStar_TypeChecker_Env.nbe)
             }))
  
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e  ->
    fun f  ->
      let uu____941 = f e.FStar_Extraction_ML_UEnv.env_tcenv  in
      match uu____941 with
      | (a,t') ->
          (a,
            (let uu___16_1233 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___16_1233.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___16_1233.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___16_1233.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___16_1233.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e  ->
    fun f  ->
      let uu____1557 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f  in
      match uu____1557 with
      | (a,tcenv) ->
          (a,
            (let uu___24_1849 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___24_1849.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___24_1849.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___24_1849.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___24_1849.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____2151 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____2272 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env"
              in
           ((), uu____2272))
       in
    FStar_Pervasives_Native.snd uu____2151
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____2678 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____2799 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____2799))
       in
    FStar_Pervasives_Native.snd uu____2678
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____3401 = pop_env env1  in res
  
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
        let uu____3977 = FStar_Parser_Driver.parse_file fn  in
        match uu____3977 with
        | (ast,uu____4061) ->
            let uu____4076 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____4266 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____4266 with
                   | (pre_ast,uu____4342) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____4422),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____4471 =
                              let uu____4535 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____4535  in
                            (match uu____4471 with
                             | (uu____4603,env1) ->
                                 let uu____4723 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____4723)
                        | uu____4729 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____4076 with
             | (ast1,env1) ->
                 let uu____4990 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____4990)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____5148 = FStar_Options.lax ()  in
      if uu____5148
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___68_5164 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___68_5164.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___68_5164.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___68_5164.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___68_5164.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___68_5164.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_sig =
             (uu___68_5164.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___68_5164.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___68_5164.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___68_5164.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____5296 =
        let uu____5373 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____5373  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____5296
       in
    let env1 =
      let uu___72_5497 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___72_5497.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___72_5497.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___72_5497.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___72_5497.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___72_5497.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___72_5497.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___72_5497.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___72_5497.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___72_5497.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___72_5497.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___72_5497.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___72_5497.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___72_5497.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___72_5497.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___72_5497.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___72_5497.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___72_5497.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___72_5497.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___72_5497.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___72_5497.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___72_5497.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___72_5497.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___72_5497.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___72_5497.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___72_5497.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___72_5497.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___72_5497.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___72_5497.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___72_5497.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___72_5497.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___72_5497.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___72_5497.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___72_5497.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___72_5497.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___72_5497.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___72_5497.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___72_5497.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___72_5497.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___72_5497.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___72_5497.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___72_5497.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___72_5497.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___75_5715 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___75_5715.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___75_5715.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___75_5715.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___75_5715.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___75_5715.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___75_5715.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___75_5715.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___75_5715.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___75_5715.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___75_5715.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___75_5715.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___75_5715.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___75_5715.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___75_5715.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___75_5715.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___75_5715.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___75_5715.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___75_5715.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___75_5715.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___75_5715.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___75_5715.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___75_5715.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___75_5715.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___75_5715.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___75_5715.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___75_5715.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___75_5715.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___75_5715.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___75_5715.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___75_5715.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___75_5715.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___75_5715.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___75_5715.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___75_5715.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___75_5715.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___75_5715.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___75_5715.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___75_5715.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___75_5715.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___75_5715.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___75_5715.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___75_5715.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___78_5933 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___78_5933.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___78_5933.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___78_5933.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___78_5933.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___78_5933.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___78_5933.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___78_5933.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___78_5933.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___78_5933.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___78_5933.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___78_5933.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___78_5933.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___78_5933.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___78_5933.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___78_5933.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___78_5933.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___78_5933.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___78_5933.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___78_5933.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___78_5933.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___78_5933.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___78_5933.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___78_5933.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___78_5933.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___78_5933.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___78_5933.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___78_5933.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___78_5933.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___78_5933.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___78_5933.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___78_5933.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___78_5933.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___78_5933.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___78_5933.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___78_5933.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___78_5933.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___78_5933.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___78_5933.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___78_5933.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___78_5933.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___78_5933.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___78_5933.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___81_6151 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___81_6151.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___81_6151.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___81_6151.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___81_6151.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___81_6151.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___81_6151.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___81_6151.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___81_6151.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___81_6151.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___81_6151.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___81_6151.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___81_6151.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___81_6151.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___81_6151.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___81_6151.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___81_6151.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___81_6151.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___81_6151.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___81_6151.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___81_6151.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___81_6151.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___81_6151.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___81_6151.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___81_6151.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___81_6151.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___81_6151.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___81_6151.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___81_6151.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___81_6151.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___81_6151.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___81_6151.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___81_6151.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___81_6151.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___81_6151.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___81_6151.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___81_6151.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___81_6151.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___81_6151.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___81_6151.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___81_6151.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___81_6151.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___81_6151.FStar_TypeChecker_Env.nbe)
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
          let uu____6502 =
            let uu____6504 =
              let uu____6506 = FStar_Options.file_list ()  in
              FStar_List.hd uu____6506  in
            FStar_Parser_Dep.lowercase_module_name uu____6504  in
          let uu____6511 =
            let uu____6513 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____6513  in
          uu____6502 = uu____6511  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____6522,{ FStar_Parser_AST.d = uu____6523;
                            FStar_Parser_AST.drange = d;
                            FStar_Parser_AST.doc = uu____6525;
                            FStar_Parser_AST.quals = uu____6526;
                            FStar_Parser_AST.attrs = uu____6527;_}::uu____6528)
              -> d
          | FStar_Parser_AST.Interface
              (uu____6558,{ FStar_Parser_AST.d = uu____6559;
                            FStar_Parser_AST.drange = d;
                            FStar_Parser_AST.doc = uu____6561;
                            FStar_Parser_AST.quals = uu____6562;
                            FStar_Parser_AST.attrs = uu____6563;_}::uu____6564,uu____6565)
              -> d
          | uu____6597 -> FStar_Range.dummyRange  in
        let uu____6598 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____6598 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____6801 =
              let uu____6860 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____6860  in
            (match uu____6801 with
             | (ast_modul1,env1) ->
                 let uu____7105 =
                   let uu____7172 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____7172
                    in
                 (match uu____7105 with
                  | (modul,env2) ->
                      ((let uu____7465 =
                          let uu____7467 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____7467  in
                        if uu____7465
                        then
                          let msg =
                            let uu____7472 =
                              let uu____7474 =
                                let uu____7476 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____7476  in
                              FStar_Parser_Dep.module_name_of_file uu____7474
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____7472
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____7485 =
                          let uu____7563 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____7563
                          then ((modul, []), env2)
                          else
                            (let uu____7738 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____7738 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____7485 with
                        | ((modul1,uu____8189),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____8504 = FStar_List.hd ast_decls  in
                 (match uu____8504 with
                  | { FStar_Parser_AST.d = uu____8588;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____8590;
                      FStar_Parser_AST.quals = uu____8591;
                      FStar_Parser_AST.attrs = uu____8592;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____8682 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____8882 =
                            let uu____8948 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____8948
                             in
                          match uu____8882 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____8682 with
                  | (env1,ast_decls_l) ->
                      let uu____9488 =
                        let uu____9547 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____9547
                         in
                      (match uu____9488 with
                       | (sigelts,env2) ->
                           let uu____9796 =
                             let uu____9872 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____9872
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____9796 with
                            | (modul1,uu____10095,env3) ->
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
           (l,decls,uu____10593)),uu____10594)
          ->
          let uu____10640 =
            let uu____10699 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____10699  in
          FStar_Pervasives_Native.snd uu____10640
      | FStar_Parser_ParseIt.ASTFragment uu____10819 ->
          let uu____10831 =
            let uu____10837 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____10837)  in
          FStar_Errors.raise_err uu____10831
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____10955 ->
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
        | uu____11039 -> failwith "Unrecognized option"  in
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
           | (name,uu____11068)::[] ->
               let uu____11071 =
                 FStar_Options.prepend_output_dir (Prims.op_Hat name ext)  in
               FStar_Util.save_value_to_file uu____11071 bin
           | uu____11073 ->
               let uu____11076 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____11076 bin)
      | uu____11079 -> failwith "Unrecognized option"
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
          (let maybe_restore_opts uu____11400 =
             let uu____11401 =
               let uu____11403 = FStar_Options.interactive ()  in
               Prims.op_Negation uu____11403  in
             if uu____11401
             then
               let uu____11406 = FStar_Options.restore_cmd_line_options true
                  in
               FStar_All.pipe_right uu____11406 (fun a1  -> ())
             else ()  in
           let post_smt_encoding uu____11415 =
             FStar_SMTEncoding_Z3.refresh ()  in
           let maybe_extract_mldefs tcmod env1 =
             let uu____11569 =
               (let uu____11573 = FStar_Options.codegen ()  in
                uu____11573 = FStar_Pervasives_Native.None) ||
                 (let uu____11579 =
                    FStar_Options.should_extract
                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  Prims.op_Negation uu____11579)
                in
             if uu____11569
             then (FStar_Pervasives_Native.None, (Prims.parse_int "0"))
             else
               FStar_Util.record_time
                 (fun uu____11605  ->
                    let uu____11606 =
                      FStar_Extraction_ML_Modul.extract env1 tcmod  in
                    match uu____11606 with | (uu____11676,defs) -> defs)
              in
           let maybe_extract_ml_iface tcmod env1 =
             let uu____12011 =
               let uu____12013 = FStar_Options.codegen ()  in
               uu____12013 = FStar_Pervasives_Native.None  in
             if uu____12011
             then (env1, (Prims.parse_int "0"))
             else
               (let uu____12146 =
                  FStar_Util.record_time
                    (fun uu____12279  ->
                       FStar_Extraction_ML_Modul.extract_iface env1 tcmod)
                   in
                match uu____12146 with
                | ((env2,_extracted_iface),iface_extract_time) ->
                    (env2, iface_extract_time))
              in
           let tc_source_file uu____12676 =
             let uu____12677 = parse env pre_fn fn  in
             match uu____12677 with
             | (fmod,env1) ->
                 let mii =
                   FStar_Syntax_DsEnv.inclusion_info
                     (env1.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                     fmod.FStar_Syntax_Syntax.name
                    in
                 let check_mod uu____13053 =
                   let uu____13054 =
                     FStar_Util.record_time
                       (fun uu____13243  ->
                          with_tcenv_of_env env1
                            (fun tcenv  ->
                               (match tcenv.FStar_TypeChecker_Env.gamma with
                                | [] -> ()
                                | uu____13335 ->
                                    failwith
                                      "Impossible: gamma contains leaked names");
                               (let uu____13339 =
                                  FStar_TypeChecker_Tc.check_module tcenv
                                    fmod (FStar_Util.is_some pre_fn)
                                   in
                                match uu____13339 with
                                | (modul,env2) ->
                                    (maybe_restore_opts ();
                                     (let smt_decls =
                                        let uu____13637 =
                                          let uu____13639 =
                                            FStar_Options.lax ()  in
                                          Prims.op_Negation uu____13639  in
                                        if uu____13637
                                        then
                                          let smt_decls =
                                            FStar_SMTEncoding_Encode.encode_modul
                                              env2 modul
                                             in
                                          (post_smt_encoding (); smt_decls)
                                        else ([], [])  in
                                      ((modul, smt_decls), env2))))))
                      in
                   match uu____13054 with
                   | (((tcmod,smt_decls),env2),tc_time) ->
                       let uu____14182 =
                         with_env env2 (maybe_extract_mldefs tcmod)  in
                       (match uu____14182 with
                        | (extracted_defs,extract_time) ->
                            let uu____14290 =
                              with_env env2 (maybe_extract_ml_iface tcmod)
                               in
                            (match uu____14290 with
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
                 let uu____14697 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                    in
                 if uu____14697
                 then
                   let uu____14781 = FStar_Parser_ParseIt.find_file fn  in
                   FStar_SMTEncoding_Solver.with_hints_db uu____14781
                     check_mod
                 else check_mod ()
              in
           let uu____14866 =
             let uu____14868 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____14868  in
           if uu____14866
           then
             let uu____14952 =
               FStar_CheckedFiles.load_module_from_cache env fn  in
             match uu____14952 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____15063 =
                     let uu____15065 =
                       FStar_Parser_Dep.module_name_of_file fn  in
                     FStar_Options.should_be_already_cached uu____15065  in
                   if uu____15063
                   then
                     let uu____15068 =
                       let uu____15074 =
                         FStar_Util.format1
                           "Expected %s to already be checked" fn
                          in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____15074)
                        in
                     FStar_Errors.raise_err uu____15068
                   else ());
                  (let uu____15081 =
                     (let uu____15085 = FStar_Options.codegen ()  in
                      FStar_Option.isSome uu____15085) &&
                       (FStar_Options.cmi ())
                      in
                   if uu____15081
                   then
                     let uu____15089 =
                       let uu____15095 =
                         FStar_Util.format1
                           "Cross-module inlining expects all modules to be checked first; %s was not checked"
                           fn
                          in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____15095)
                        in
                     FStar_Errors.raise_err uu____15089
                   else ());
                  (let uu____15101 = tc_source_file ()  in
                   match uu____15101 with
                   | (tc_result,mllib,env1) ->
                       ((let uu____15418 =
                           (let uu____15422 = FStar_Errors.get_err_count ()
                               in
                            uu____15422 = (Prims.parse_int "0")) &&
                             ((FStar_Options.lax ()) ||
                                (FStar_Options.should_verify
                                   ((tc_result.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                            in
                         if uu____15418
                         then
                           FStar_CheckedFiles.store_module_to_cache env1 fn
                             parsing_data tc_result
                         else ());
                        (tc_result, mllib, env1))))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.FStar_CheckedFiles.checked_module  in
                 let smt_decls = tc_result.FStar_CheckedFiles.smt_decls  in
                 ((let uu____15566 =
                     FStar_Options.dump_module
                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____15566
                   then
                     let uu____15569 =
                       FStar_Syntax_Print.modul_to_string tcmod  in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____15569
                   else ());
                  (let extend_tcenv tcmod1 tcenv =
                     let uu____15767 =
                       let uu____15826 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                           tc_result.FStar_CheckedFiles.mii
                           (FStar_TypeChecker_Normalize.erase_universes tcenv)
                          in
                       FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                         uu____15826
                        in
                     match uu____15767 with
                     | (uu____15950,tcenv1) ->
                         let env1 =
                           FStar_TypeChecker_Tc.load_checked_module tcenv1
                             tcmod1
                            in
                         (maybe_restore_opts ();
                          (let uu____16171 =
                             let uu____16173 = FStar_Options.lax ()  in
                             Prims.op_Negation uu____16173  in
                           if uu____16171
                           then
                             (FStar_SMTEncoding_Encode.encode_modul_from_cache
                                env1 tcmod1.FStar_Syntax_Syntax.name
                                smt_decls;
                              post_smt_encoding ())
                           else ());
                          ((), env1))
                      in
                   let env1 =
                     FStar_Options.profile
                       (fun uu____16413  ->
                          let uu____16414 =
                            with_tcenv_of_env env (extend_tcenv tcmod)  in
                          FStar_All.pipe_right uu____16414
                            FStar_Pervasives_Native.snd)
                       (fun uu____16660  ->
                          FStar_Util.format1
                            "Extending environment with module %s"
                            (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                      in
                   let mllib =
                     let uu____16725 =
                       ((let uu____16729 = FStar_Options.codegen ()  in
                         uu____16729 <> FStar_Pervasives_Native.None) &&
                          (FStar_Options.should_extract
                             (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                         &&
                         ((Prims.op_Negation
                             tcmod.FStar_Syntax_Syntax.is_interface)
                            ||
                            (let uu____16735 = FStar_Options.codegen ()  in
                             uu____16735 =
                               (FStar_Pervasives_Native.Some
                                  FStar_Options.Kremlin)))
                        in
                     if uu____16725
                     then
                       with_env env1
                         (fun env2  ->
                            let uu____16811 = maybe_extract_mldefs tcmod env2
                               in
                            match uu____16811 with
                            | (extracted_defs,_extraction_time) ->
                                extracted_defs)
                     else FStar_Pervasives_Native.None  in
                   let uu____16836 =
                     with_env env1 (maybe_extract_ml_iface tcmod)  in
                   match uu____16836 with
                   | (env2,_time) -> (tc_result, mllib, env2)))
           else
             (let uu____17245 = tc_source_file ()  in
              match uu____17245 with
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
          let uu____18034 = tc_one_file env1 pre_fn fn parsing_data  in
          match uu____18034 with
          | (tc_result,uu____18188,env2) ->
              (tc_result, (env2.FStar_Extraction_ML_UEnv.env_tcenv))
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____18429 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____18429 ["fsti"; "fsi"]))
        &&
        (let uu____18438 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____18438 ["fst"; "fs"])
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      FStar_Parser_Dep.deps ->
        (Prims.string Prims.list * FStar_CheckedFiles.tc_result Prims.list *
          FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option *
          uenv))
  =
  fun remaining  ->
    fun env  ->
      fun deps  ->
        let uu____18674 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____18865 =
                let uu____18947 =
                  FStar_All.pipe_right impl
                    (FStar_Parser_Dep.parsing_data_of deps)
                   in
                tc_one_file env (FStar_Pervasives_Native.Some intf) impl
                  uu____18947
                 in
              (match uu____18865 with
               | (m,mllib,env1) -> (remaining1, ([m], mllib, env1)))
          | intf_or_impl::remaining1 ->
              let uu____19389 =
                let uu____19471 =
                  FStar_All.pipe_right intf_or_impl
                    (FStar_Parser_Dep.parsing_data_of deps)
                   in
                tc_one_file env FStar_Pervasives_Native.None intf_or_impl
                  uu____19471
                 in
              (match uu____19389 with
               | (m,mllib,env1) -> (remaining1, ([m], mllib, env1)))
          | [] -> ([], ([], FStar_Pervasives_Native.None, env))  in
        match uu____18674 with
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
        let as_list uu___0_20782 =
          match uu___0_20782 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some l -> [l]  in
        match remaining with
        | [] -> acc
        | uu____20880 ->
            let uu____20884 = acc  in
            (match uu____20884 with
             | (mods,mllibs,env) ->
                 let uu____21208 =
                   tc_one_file_from_remaining remaining env deps  in
                 (match uu____21208 with
                  | (remaining1,nmods,mllib,env1) ->
                      tc_fold_interleave deps
                        ((FStar_List.append mods nmods),
                          (FStar_List.append mllibs (as_list mllib)), env1)
                        remaining1))
  
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      (FStar_CheckedFiles.tc_result Prims.list * uenv * (uenv -> uenv)))
  =
  fun filenames  ->
    fun dep_graph1  ->
      (let uu____21854 = FStar_Options.debug_any ()  in
       if uu____21854
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____21862 =
             let uu____21864 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____21864  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____21862))
       else ());
      (let env =
         let uu____21998 = init_env dep_graph1  in
         FStar_Extraction_ML_UEnv.mkContext uu____21998  in
       let uu____22107 =
         tc_fold_interleave dep_graph1 ([], [], env) filenames  in
       match uu____22107 with
       | (all_mods,mllibs,env1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____22824 =
                 with_tcenv_of_env env2
                   (fun tcenv  ->
                      (let uu____22946 =
                         (FStar_Options.interactive ()) &&
                           (let uu____22949 = FStar_Errors.get_err_count ()
                               in
                            uu____22949 = (Prims.parse_int "0"))
                          in
                       if uu____22946
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv))
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____22824
                in
             (all_mods, env1, solver_refresh))))
  