open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "7") 
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul -> (Prims.bool * FStar_Ident.lident)) =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
  
type uenv = FStar_Extraction_ML_UEnv.uenv
type tc_result =
  {
  checked_module: FStar_Syntax_Syntax.modul ;
  mii: FStar_Syntax_DsEnv.module_inclusion_info ;
  tc_time: Prims.int ;
  extraction_time: Prims.int }
let (__proj__Mktc_result__item__checked_module :
  tc_result -> FStar_Syntax_Syntax.modul) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; tc_time; extraction_time;_} -> checked_module
  
let (__proj__Mktc_result__item__mii :
  tc_result -> FStar_Syntax_DsEnv.module_inclusion_info) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; tc_time; extraction_time;_} -> mii
  
let (__proj__Mktc_result__item__tc_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; tc_time; extraction_time;_} -> tc_time
  
let (__proj__Mktc_result__item__extraction_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; tc_time; extraction_time;_} -> extraction_time
  
let with_dsenv_of_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_Syntax_DsEnv.withenv -> ('a * FStar_TypeChecker_Env.env)
  =
  fun tcenv  ->
    fun f  ->
      let uu____121 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____121 with
      | (a,dsenv1) ->
          (a,
            (let uu___462_135 = tcenv  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___462_135.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___462_135.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___462_135.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___462_135.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___462_135.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___462_135.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___462_135.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___462_135.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___462_135.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___462_135.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___462_135.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___462_135.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___462_135.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___462_135.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___462_135.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___462_135.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___462_135.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___462_135.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___462_135.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___462_135.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___462_135.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___462_135.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___462_135.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___462_135.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___462_135.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___462_135.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___462_135.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___462_135.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___462_135.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___462_135.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___462_135.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___462_135.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___462_135.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___462_135.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___462_135.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___462_135.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___462_135.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___462_135.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___462_135.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___462_135.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___462_135.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___462_135.FStar_TypeChecker_Env.nbe)
             }))
  
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e  ->
    fun f  ->
      let uu____171 = f e.FStar_Extraction_ML_UEnv.env_tcenv  in
      match uu____171 with
      | (a,t') ->
          (a,
            (let uu___463_183 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___463_183.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___463_183.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___463_183.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___463_183.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e  ->
    fun f  ->
      let uu____216 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f  in
      match uu____216 with
      | (a,tcenv) ->
          (a,
            (let uu___464_232 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___464_232.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___464_232.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___464_232.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___464_232.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____239 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____247 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env"
              in
           ((), uu____247))
       in
    FStar_Pervasives_Native.snd uu____239
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____255 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____263 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____263))
       in
    FStar_Pervasives_Native.snd uu____255
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____290 = pop_env env1  in res
  
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
        let uu____329 = FStar_Parser_Driver.parse_file fn  in
        match uu____329 with
        | (ast,uu____346) ->
            let uu____361 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____374 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____374 with
                   | (pre_ast,uu____391) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____412),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____425 =
                              let uu____430 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____430  in
                            (match uu____425 with
                             | (uu____443,env1) ->
                                 let uu____445 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____445)
                        | uu____455 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____361 with
             | (ast1,env1) ->
                 let uu____472 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____472)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____488 = FStar_Options.lax ()  in
      if uu____488
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___465_493 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___465_493.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___465_493.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___465_493.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___465_493.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___465_493.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_modul =
             (uu___465_493.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___465_493.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___465_493.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___465_493.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___465_493.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____495 =
        let uu____510 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____510  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____495
       in
    let env1 =
      let uu___466_514 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___466_514.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___466_514.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___466_514.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___466_514.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___466_514.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___466_514.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___466_514.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___466_514.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___466_514.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___466_514.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___466_514.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___466_514.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___466_514.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___466_514.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___466_514.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___466_514.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___466_514.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___466_514.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___466_514.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___466_514.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___466_514.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___466_514.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___466_514.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___466_514.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___466_514.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___466_514.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___466_514.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___466_514.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___466_514.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___466_514.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___466_514.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___466_514.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___466_514.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___466_514.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___466_514.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___466_514.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___466_514.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___466_514.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___466_514.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___466_514.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___466_514.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___466_514.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___467_516 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___467_516.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___467_516.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___467_516.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___467_516.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___467_516.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___467_516.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___467_516.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___467_516.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___467_516.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___467_516.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___467_516.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___467_516.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___467_516.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___467_516.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___467_516.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___467_516.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___467_516.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___467_516.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___467_516.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___467_516.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___467_516.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___467_516.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___467_516.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___467_516.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___467_516.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___467_516.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___467_516.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___467_516.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___467_516.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___467_516.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___467_516.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___467_516.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___467_516.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___467_516.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___467_516.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___467_516.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___467_516.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___467_516.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___467_516.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___467_516.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___467_516.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___467_516.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___468_518 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___468_518.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___468_518.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___468_518.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___468_518.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___468_518.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___468_518.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___468_518.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___468_518.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___468_518.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___468_518.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___468_518.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___468_518.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___468_518.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___468_518.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___468_518.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___468_518.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___468_518.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___468_518.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___468_518.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___468_518.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___468_518.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___468_518.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___468_518.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___468_518.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___468_518.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___468_518.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___468_518.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___468_518.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___468_518.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___468_518.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___468_518.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___468_518.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___468_518.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___468_518.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___468_518.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___468_518.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___468_518.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___468_518.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___468_518.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___468_518.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___468_518.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___468_518.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___469_520 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___469_520.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___469_520.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___469_520.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___469_520.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___469_520.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___469_520.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___469_520.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___469_520.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___469_520.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___469_520.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___469_520.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___469_520.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___469_520.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___469_520.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___469_520.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___469_520.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___469_520.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___469_520.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___469_520.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___469_520.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___469_520.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___469_520.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___469_520.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___469_520.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___469_520.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___469_520.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___469_520.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___469_520.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___469_520.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___469_520.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___469_520.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___469_520.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___469_520.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___469_520.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___469_520.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___469_520.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___469_520.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___469_520.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___469_520.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___469_520.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___469_520.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___469_520.FStar_TypeChecker_Env.nbe)
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
          let uu____555 =
            let uu____557 =
              let uu____559 = FStar_Options.file_list ()  in
              FStar_List.hd uu____559  in
            FStar_Parser_Dep.lowercase_module_name uu____557  in
          let uu____564 =
            let uu____566 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____566  in
          uu____555 = uu____564  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____575,{ FStar_Parser_AST.d = uu____576;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____578;
                           FStar_Parser_AST.quals = uu____579;
                           FStar_Parser_AST.attrs = uu____580;_}::uu____581)
              -> d
          | FStar_Parser_AST.Interface
              (uu____588,{ FStar_Parser_AST.d = uu____589;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____591;
                           FStar_Parser_AST.quals = uu____592;
                           FStar_Parser_AST.attrs = uu____593;_}::uu____594,uu____595)
              -> d
          | uu____604 -> FStar_Range.dummyRange  in
        let uu____605 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____605 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____617 =
              let uu____622 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____622  in
            (match uu____617 with
             | (ast_modul1,env1) ->
                 let uu____647 =
                   let uu____652 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____652
                    in
                 (match uu____647 with
                  | (modul,env2) ->
                      ((let uu____677 =
                          let uu____679 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____679  in
                        if uu____677
                        then
                          let msg =
                            let uu____684 =
                              let uu____686 =
                                let uu____688 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____688  in
                              FStar_Parser_Dep.module_name_of_file uu____686
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____684
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____697 =
                          let uu____708 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____708
                          then ((modul, []), env2)
                          else
                            (let uu____731 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____731 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____697 with
                        | ((modul1,uu____772),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____795 = FStar_List.hd ast_decls  in
                 (match uu____795 with
                  | { FStar_Parser_AST.d = uu____802;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____804;
                      FStar_Parser_AST.quals = uu____805;
                      FStar_Parser_AST.attrs = uu____806;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____818 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____836 =
                            let uu____843 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____843
                             in
                          match uu____836 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____818 with
                  | (env1,ast_decls_l) ->
                      let uu____897 =
                        let uu____902 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____902
                         in
                      (match uu____897 with
                       | (sigelts,env2) ->
                           let uu____926 =
                             let uu____935 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____935
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____926 with
                            | (modul1,uu____957,env3) ->
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
           (l,decls,uu____981)),uu____982)
          ->
          let uu____1005 =
            let uu____1010 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____1010  in
          FStar_Pervasives_Native.snd uu____1005
      | FStar_Parser_ParseIt.ASTFragment uu____1026 ->
          let uu____1038 =
            let uu____1044 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____1044)  in
          FStar_Errors.raise_err uu____1038
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____1054 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
  
let (load_module_from_cache :
  uenv -> Prims.string -> tc_result FStar_Pervasives_Native.option) =
  let some_cache_invalid = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let invalidate_cache fn =
    FStar_ST.op_Colon_Equals some_cache_invalid
      (FStar_Pervasives_Native.Some ())
     in
  let load1 env source_file cache_file =
    let uu____1151 = FStar_Util.load_value_from_file cache_file  in
    match uu____1151 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inl "Corrupt"
    | FStar_Pervasives_Native.Some (vnum,digest,tc_result) ->
        if vnum <> cache_version_number
        then FStar_Util.Inl "Stale, because inconsistent cache version"
        else
          (let uu____1253 =
             let uu____1264 = FStar_TypeChecker_Env.dep_graph env  in
             FStar_Parser_Dep.hash_dependences uu____1264 source_file
               cache_file
              in
           match uu____1253 with
           | FStar_Pervasives_Native.Some digest' ->
               if digest = digest'
               then FStar_Util.Inr tc_result
               else
                 ((let uu____1305 = FStar_Options.debug_any ()  in
                   if uu____1305
                   then
                     ((let uu____1309 =
                         FStar_Util.string_of_int (FStar_List.length digest')
                          in
                       let uu____1317 = FStar_Parser_Dep.print_digest digest'
                          in
                       let uu____1319 =
                         FStar_Util.string_of_int (FStar_List.length digest)
                          in
                       let uu____1327 = FStar_Parser_Dep.print_digest digest
                          in
                       FStar_Util.print4
                         "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                         uu____1309 uu____1317 uu____1319 uu____1327);
                      if
                        (FStar_List.length digest) =
                          (FStar_List.length digest')
                      then
                        FStar_List.iter2
                          (fun uu____1363  ->
                             fun uu____1364  ->
                               match (uu____1363, uu____1364) with
                               | ((x,y),(x',y')) ->
                                   if (x <> x') || (y <> y')
                                   then
                                     let uu____1416 =
                                       FStar_Parser_Dep.print_digest [(x, y)]
                                        in
                                     let uu____1432 =
                                       FStar_Parser_Dep.print_digest
                                         [(x', y')]
                                        in
                                     FStar_Util.print2
                                       "Differ at: Expected %s\n Got %s\n"
                                       uu____1416 uu____1432
                                   else ()) digest digest'
                      else ())
                   else ());
                  FStar_Util.Inl "Stale")
           | uu____1457 -> FStar_Util.Inl "Unable to compute digest of")
     in
  fun env  ->
    fun fn  ->
      let load_it uu____1480 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn  in
        let fail1 maybe_warn cache_file1 =
          invalidate_cache ();
          (match maybe_warn with
           | FStar_Pervasives_Native.None  -> ()
           | FStar_Pervasives_Native.Some tag ->
               let uu____1507 =
                 let uu____1508 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 let uu____1511 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 FStar_Range.mk_range fn uu____1508 uu____1511  in
               let uu____1514 =
                 let uu____1520 =
                   FStar_Util.format3
                     "%s cache file %s; will recheck %s and all subsequent files"
                     tag cache_file1 fn
                    in
                 (FStar_Errors.Warning_CachedFile, uu____1520)  in
               FStar_Errors.log_issue uu____1507 uu____1514)
           in
        let uu____1524 = FStar_ST.op_Bang some_cache_invalid  in
        match uu____1524 with
        | FStar_Pervasives_Native.Some uu____1574 ->
            FStar_Pervasives_Native.None
        | uu____1575 ->
            if Prims.op_Negation (FStar_Util.file_exists cache_file)
            then FStar_Pervasives_Native.None
            else
              (let uu____1583 =
                 load1 env.FStar_Extraction_ML_UEnv.env_tcenv fn cache_file
                  in
               match uu____1583 with
               | FStar_Util.Inl msg ->
                   (fail1 (FStar_Pervasives_Native.Some msg) cache_file;
                    FStar_Pervasives_Native.None)
               | FStar_Util.Inr res -> FStar_Pervasives_Native.Some res)
         in
      FStar_Options.profile load_it
        (fun res  ->
           let msg = if FStar_Option.isSome res then "ok" else "failed"  in
           let uu____1614 = FStar_Parser_Dep.cache_file_name fn  in
           FStar_Util.format2 "Loading checked file %s ... %s" uu____1614 msg)
  
let (store_module_to_cache : uenv -> Prims.string -> tc_result -> unit) =
  fun env  ->
    fun fn  ->
      fun tc_result  ->
        let uu____1635 =
          (FStar_Options.cache_checked_modules ()) &&
            (let uu____1638 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____1638)
           in
        if uu____1635
        then
          let cache_file = FStar_Parser_Dep.cache_file_name fn  in
          let digest =
            let uu____1654 =
              FStar_TypeChecker_Env.dep_graph
                env.FStar_Extraction_ML_UEnv.env_tcenv
               in
            FStar_Parser_Dep.hash_dependences uu____1654 fn cache_file  in
          match digest with
          | FStar_Pervasives_Native.Some hashes ->
              let tc_result1 =
                let uu___470_1673 = tc_result  in
                {
                  checked_module = (uu___470_1673.checked_module);
                  mii = (uu___470_1673.mii);
                  tc_time = (Prims.parse_int "0");
                  extraction_time = (uu___470_1673.extraction_time)
                }  in
              FStar_Util.save_value_to_file cache_file
                (cache_version_number, hashes, tc_result1)
          | uu____1699 ->
              let uu____1710 =
                let uu____1711 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                let uu____1714 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range fn uu____1711 uu____1714  in
              let uu____1717 =
                let uu____1723 =
                  FStar_Util.format1
                    "%s was not written, since some of its dependences were not also checked"
                    cache_file
                   in
                (FStar_Errors.Warning_FileNotWritten, uu____1723)  in
              FStar_Errors.log_issue uu____1710 uu____1717
        else ()
  
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
            ((fun e  -> let uu____1807 = f1 e  in g uu____1807))
  
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
        | uu____1831 -> failwith "Unrecognized option"  in
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
           | (name,uu____1856)::[] ->
               let uu____1859 =
                 FStar_Options.prepend_output_dir (Prims.strcat name ext)  in
               FStar_Util.save_value_to_file uu____1859 bin
           | uu____1861 ->
               let uu____1864 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____1864 bin)
      | uu____1867 -> failwith "Unrecognized option"
    else ()
  
let (tc_one_file :
  uenv ->
    delta_env ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          (tc_result * FStar_Extraction_ML_Syntax.mllib
            FStar_Pervasives_Native.option * uenv * delta_env))
  =
  fun env  ->
    fun delta1  ->
      fun pre_fn  ->
        fun fn  ->
          FStar_Syntax_Syntax.reset_gensym ();
          (let maybe_extract_mldefs tcmod env1 =
             let uu____1943 =
               (let uu____1947 = FStar_Options.codegen ()  in
                uu____1947 = FStar_Pervasives_Native.None) ||
                 (let uu____1953 =
                    FStar_Options.should_extract
                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  Prims.op_Negation uu____1953)
                in
             if uu____1943
             then (FStar_Pervasives_Native.None, (Prims.parse_int "0"))
             else
               FStar_Util.record_time
                 (fun uu____1975  ->
                    let uu____1976 =
                      FStar_Extraction_ML_Modul.extract env1 tcmod  in
                    match uu____1976 with | (uu____1985,defs) -> defs)
              in
           let maybe_extract_ml_iface tcmod env1 =
             let uu____2007 =
               let uu____2009 = FStar_Options.codegen ()  in
               uu____2009 = FStar_Pervasives_Native.None  in
             if uu____2007
             then (env1, (Prims.parse_int "0"))
             else
               (let uu____2024 =
                  FStar_Util.record_time
                    (fun uu____2039  ->
                       FStar_Extraction_ML_Modul.extract_iface env1 tcmod)
                   in
                match uu____2024 with
                | ((env2,_extracted_iface),iface_extract_time) ->
                    (env2, iface_extract_time))
              in
           let tc_source_file uu____2068 =
             let env1 = apply_delta_env env delta1  in
             let uu____2072 = parse env1 pre_fn fn  in
             match uu____2072 with
             | (fmod,env2) ->
                 let mii =
                   FStar_Syntax_DsEnv.inclusion_info
                     (env2.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                     fmod.FStar_Syntax_Syntax.name
                    in
                 let check_mod uu____2101 =
                   let uu____2102 =
                     FStar_Util.record_time
                       (fun uu____2117  ->
                          with_tcenv_of_env env2
                            (fun tcenv  ->
                               (match tcenv.FStar_TypeChecker_Env.gamma with
                                | [] -> ()
                                | uu____2122 ->
                                    failwith
                                      "Impossible: gamma contains leaked names");
                               FStar_TypeChecker_Tc.check_module tcenv fmod
                                 (FStar_Util.is_some pre_fn)))
                      in
                   match uu____2102 with
                   | ((tcmod,env3),tc_time) ->
                       let uu____2144 =
                         with_env env3 (maybe_extract_mldefs tcmod)  in
                       (match uu____2144 with
                        | (extracted_defs,extract_time) ->
                            let uu____2175 =
                              with_env env3 (maybe_extract_ml_iface tcmod)
                               in
                            (match uu____2175 with
                             | (env4,iface_extraction_time) ->
                                 ({
                                    checked_module = tcmod;
                                    mii;
                                    tc_time;
                                    extraction_time =
                                      (extract_time + iface_extraction_time)
                                  }, extracted_defs, env4)))
                    in
                 let uu____2200 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                    in
                 if uu____2200
                 then
                   let uu____2211 = FStar_Parser_ParseIt.find_file fn  in
                   FStar_SMTEncoding_Solver.with_hints_db uu____2211
                     check_mod
                 else check_mod ()
              in
           let uu____2223 =
             let uu____2225 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____2225  in
           if uu____2223
           then
             let uu____2238 = load_module_from_cache env fn  in
             match uu____2238 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____2252 =
                     let uu____2254 = FStar_Parser_Dep.module_name_of_file fn
                        in
                     FStar_Options.should_be_already_cached uu____2254  in
                   if uu____2252
                   then
                     let uu____2257 =
                       let uu____2263 =
                         FStar_Util.format1
                           "Expected %s to already be checked" fn
                          in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____2263)
                        in
                     FStar_Errors.raise_err uu____2257
                   else ());
                  (let uu____2270 =
                     (let uu____2274 = FStar_Options.codegen ()  in
                      FStar_Option.isSome uu____2274) &&
                       (FStar_Options.cmi ())
                      in
                   if uu____2270
                   then
                     let uu____2278 =
                       let uu____2284 =
                         FStar_Util.format1
                           "Cross-module inlining expects all modules to be checked first; %s was not checked"
                           fn
                          in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____2284)
                        in
                     FStar_Errors.raise_err uu____2278
                   else ());
                  (let uu____2290 = tc_source_file ()  in
                   match uu____2290 with
                   | (tc_result,mllib,env1) ->
                       ((let uu____2317 =
                           (let uu____2321 = FStar_Errors.get_err_count ()
                               in
                            uu____2321 = (Prims.parse_int "0")) &&
                             ((FStar_Options.lax ()) ||
                                (FStar_Options.should_verify
                                   ((tc_result.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                            in
                         if uu____2317
                         then store_module_to_cache env1 fn tc_result
                         else ());
                        (tc_result, mllib, env1,
                          FStar_Pervasives_Native.None))))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.checked_module  in
                 ((let uu____2336 =
                     FStar_Options.dump_module
                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____2336
                   then
                     let uu____2339 =
                       FStar_Syntax_Print.modul_to_string tcmod  in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____2339
                   else ());
                  (let delta_tcenv tcmod1 tcenv =
                     let uu____2359 =
                       let uu____2364 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                           tc_result.mii
                           (FStar_TypeChecker_Normalize.erase_universes tcenv)
                          in
                       FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                         uu____2364
                        in
                     match uu____2359 with
                     | (uu____2384,tcenv1) ->
                         let uu____2386 =
                           FStar_TypeChecker_Tc.load_checked_module tcenv1
                             tcmod1
                            in
                         ((), uu____2386)
                      in
                   let mllib =
                     let uu____2390 =
                       ((let uu____2394 = FStar_Options.codegen ()  in
                         uu____2394 <> FStar_Pervasives_Native.None) &&
                          (FStar_Options.should_extract
                             (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                         &&
                         ((Prims.op_Negation
                             tcmod.FStar_Syntax_Syntax.is_interface)
                            ||
                            (let uu____2400 = FStar_Options.codegen ()  in
                             uu____2400 =
                               (FStar_Pervasives_Native.Some
                                  FStar_Options.Kremlin)))
                        in
                     if uu____2390
                     then
                       with_env env
                         (fun env1  ->
                            let env2 = apply_delta_env env1 delta1  in
                            let extract_defs tcmod1 env3 =
                              let uu____2438 =
                                with_tcenv_of_env env3 (delta_tcenv tcmod1)
                                 in
                              match uu____2438 with
                              | (uu____2450,env4) ->
                                  maybe_extract_mldefs tcmod1 env4
                               in
                            let uu____2452 = extract_defs tcmod env2  in
                            match uu____2452 with
                            | (extracted_defs,extraction_time) ->
                                extracted_defs)
                     else FStar_Pervasives_Native.None  in
                   let delta_env env1 =
                     FStar_Options.profile
                       (fun uu____2485  ->
                          let uu____2486 =
                            with_tcenv_of_env env1 (delta_tcenv tcmod)  in
                          match uu____2486 with
                          | (uu____2491,env2) ->
                              let uu____2493 =
                                with_env env2 (maybe_extract_ml_iface tcmod)
                                 in
                              (match uu____2493 with | (env3,_time) -> env3))
                       (fun uu____2509  ->
                          FStar_Util.format1
                            "Extending environment with module %s"
                            (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                      in
                   (tc_result, mllib, env,
                     (extend_delta_env delta1 delta_env))))
           else
             (let uu____2518 = tc_source_file ()  in
              match uu____2518 with
              | (tc_result,mllib,env1) ->
                  (tc_result, mllib, env1, FStar_Pervasives_Native.None)))
  
let (tc_one_file_for_ide :
  FStar_TypeChecker_Env.env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> (tc_result * FStar_TypeChecker_Env.env_t))
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let env1 = env_of_tcenv env  in
        let uu____2582 =
          tc_one_file env1 FStar_Pervasives_Native.None pre_fn fn  in
        match uu____2582 with
        | (tc_result,uu____2601,env2,delta1) ->
            let uu____2608 =
              let uu____2609 = apply_delta_env env2 delta1  in
              uu____2609.FStar_Extraction_ML_UEnv.env_tcenv  in
            (tc_result, uu____2608)
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____2634 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____2634 ["fsti"; "fsi"]))
        &&
        (let uu____2643 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____2643 ["fst"; "fs"])
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      delta_env ->
        (Prims.string Prims.list * tc_result Prims.list *
          FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option *
          uenv * delta_env))
  =
  fun remaining  ->
    fun env  ->
      fun delta_env  ->
        let uu____2692 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____2741 =
                tc_one_file env delta_env (FStar_Pervasives_Native.Some intf)
                  impl
                 in
              (match uu____2741 with
               | (m,mllib,env1,delta_env1) ->
                   (remaining1, ([m], mllib, env1, delta_env1)))
          | intf_or_impl::remaining1 ->
              let uu____2810 =
                tc_one_file env delta_env FStar_Pervasives_Native.None
                  intf_or_impl
                 in
              (match uu____2810 with
               | (m,mllib,env1,delta_env1) ->
                   (remaining1, ([m], mllib, env1, delta_env1)))
          | [] -> ([], ([], FStar_Pervasives_Native.None, env, delta_env))
           in
        match uu____2692 with
        | (remaining1,(nmods,mllib,env1,delta_env1)) ->
            (remaining1, nmods, mllib, env1, delta_env1)
  
let rec (tc_fold_interleave :
  (tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib Prims.list * uenv
    * delta_env) ->
    Prims.string Prims.list ->
      (tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib Prims.list *
        uenv * delta_env))
  =
  fun acc  ->
    fun remaining  ->
      let as_list uu___461_3014 =
        match uu___461_3014 with
        | FStar_Pervasives_Native.None  -> []
        | FStar_Pervasives_Native.Some l -> [l]  in
      match remaining with
      | [] -> acc
      | uu____3033 ->
          let uu____3037 = acc  in
          (match uu____3037 with
           | (mods,mllibs,env,delta_env) ->
               let uu____3074 =
                 tc_one_file_from_remaining remaining env delta_env  in
               (match uu____3074 with
                | (remaining1,nmods,mllib,env1,delta_env1) ->
                    tc_fold_interleave
                      ((FStar_List.append mods nmods),
                        (FStar_List.append mllibs (as_list mllib)), env1,
                        delta_env1) remaining1))
  
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      (tc_result Prims.list * uenv * (uenv -> uenv)
        FStar_Pervasives_Native.option))
  =
  fun filenames  ->
    fun dep_graph1  ->
      (let uu____3162 = FStar_Options.debug_any ()  in
       if uu____3162
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____3170 =
             let uu____3172 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____3172  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____3170))
       else ());
      (let env =
         let uu____3188 = init_env dep_graph1  in
         FStar_Extraction_ML_UEnv.mkContext uu____3188  in
       let uu____3189 =
         tc_fold_interleave ([], [], env, FStar_Pervasives_Native.None)
           filenames
          in
       match uu____3189 with
       | (all_mods,mllibs,env1,delta1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____3241 =
                 with_tcenv_of_env env2
                   (fun tcenv  ->
                      (let uu____3250 =
                         (FStar_Options.interactive ()) &&
                           (let uu____3253 = FStar_Errors.get_err_count ()
                               in
                            uu____3253 = (Prims.parse_int "0"))
                          in
                       if uu____3250
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv))
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____3241  in
             (all_mods, env1, (extend_delta_env delta1 solver_refresh)))))
  