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
  smt_decls:
    (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
      Prims.list)
    ;
  tc_time: Prims.int ;
  extraction_time: Prims.int }
let (__proj__Mktc_result__item__checked_module :
  tc_result -> FStar_Syntax_Syntax.modul) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        checked_module
  
let (__proj__Mktc_result__item__mii :
  tc_result -> FStar_Syntax_DsEnv.module_inclusion_info) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} -> mii
  
let (__proj__Mktc_result__item__smt_decls :
  tc_result ->
    (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding
      Prims.list))
  =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        smt_decls
  
let (__proj__Mktc_result__item__tc_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        tc_time
  
let (__proj__Mktc_result__item__extraction_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; mii; smt_decls; tc_time; extraction_time;_} ->
        extraction_time
  
let with_dsenv_of_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_Syntax_DsEnv.withenv -> ('a * FStar_TypeChecker_Env.env)
  =
  fun tcenv  ->
    fun f  ->
      let uu____191 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____191 with
      | (a,dsenv1) ->
          (a,
            (let uu___463_205 = tcenv  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___463_205.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___463_205.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___463_205.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___463_205.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___463_205.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___463_205.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___463_205.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___463_205.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___463_205.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___463_205.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___463_205.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___463_205.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___463_205.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___463_205.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___463_205.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___463_205.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___463_205.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___463_205.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___463_205.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___463_205.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___463_205.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___463_205.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___463_205.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___463_205.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___463_205.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___463_205.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___463_205.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___463_205.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___463_205.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___463_205.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___463_205.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___463_205.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___463_205.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___463_205.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___463_205.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___463_205.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___463_205.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___463_205.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___463_205.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___463_205.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___463_205.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___463_205.FStar_TypeChecker_Env.nbe)
             }))
  
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e  ->
    fun f  ->
      let uu____241 = f e.FStar_Extraction_ML_UEnv.env_tcenv  in
      match uu____241 with
      | (a,t') ->
          (a,
            (let uu___464_253 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___464_253.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___464_253.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___464_253.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___464_253.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e  ->
    fun f  ->
      let uu____286 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f  in
      match uu____286 with
      | (a,tcenv) ->
          (a,
            (let uu___465_302 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___465_302.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___465_302.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___465_302.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___465_302.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____309 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____317 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env"
              in
           ((), uu____317))
       in
    FStar_Pervasives_Native.snd uu____309
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____325 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____333 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____333))
       in
    FStar_Pervasives_Native.snd uu____325
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____360 = pop_env env1  in res
  
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
        let uu____399 = FStar_Parser_Driver.parse_file fn  in
        match uu____399 with
        | (ast,uu____416) ->
            let uu____431 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____444 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____444 with
                   | (pre_ast,uu____461) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____482),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____495 =
                              let uu____500 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____500  in
                            (match uu____495 with
                             | (uu____513,env1) ->
                                 let uu____515 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____515)
                        | uu____525 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____431 with
             | (ast1,env1) ->
                 let uu____542 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____542)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____558 = FStar_Options.lax ()  in
      if uu____558
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___466_563 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___466_563.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___466_563.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___466_563.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___466_563.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___466_563.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_sig =
             (uu___466_563.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___466_563.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___466_563.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___466_563.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____565 =
        let uu____580 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____580  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____565
       in
    let env1 =
      let uu___467_584 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___467_584.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___467_584.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___467_584.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___467_584.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___467_584.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___467_584.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___467_584.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___467_584.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___467_584.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___467_584.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___467_584.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___467_584.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___467_584.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___467_584.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___467_584.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___467_584.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___467_584.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___467_584.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___467_584.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___467_584.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___467_584.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___467_584.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___467_584.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___467_584.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___467_584.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___467_584.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___467_584.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___467_584.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___467_584.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___467_584.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___467_584.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___467_584.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___467_584.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___467_584.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___467_584.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___467_584.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___467_584.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___467_584.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___467_584.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___467_584.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___467_584.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___467_584.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___468_586 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___468_586.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___468_586.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___468_586.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___468_586.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___468_586.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___468_586.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___468_586.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___468_586.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___468_586.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___468_586.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___468_586.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___468_586.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___468_586.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___468_586.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___468_586.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___468_586.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___468_586.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___468_586.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___468_586.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___468_586.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___468_586.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___468_586.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___468_586.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___468_586.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___468_586.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___468_586.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___468_586.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___468_586.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___468_586.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___468_586.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___468_586.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___468_586.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___468_586.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___468_586.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___468_586.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___468_586.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___468_586.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___468_586.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___468_586.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___468_586.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___468_586.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___468_586.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___469_588 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___469_588.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___469_588.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___469_588.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___469_588.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___469_588.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___469_588.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___469_588.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___469_588.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___469_588.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___469_588.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___469_588.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___469_588.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___469_588.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___469_588.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___469_588.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___469_588.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___469_588.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___469_588.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___469_588.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___469_588.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___469_588.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___469_588.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___469_588.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___469_588.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___469_588.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___469_588.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___469_588.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___469_588.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___469_588.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___469_588.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___469_588.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___469_588.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___469_588.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___469_588.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___469_588.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___469_588.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___469_588.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___469_588.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___469_588.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___469_588.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___469_588.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___469_588.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___470_590 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___470_590.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___470_590.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___470_590.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___470_590.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___470_590.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___470_590.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___470_590.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___470_590.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___470_590.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___470_590.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___470_590.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___470_590.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___470_590.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___470_590.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___470_590.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___470_590.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___470_590.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___470_590.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___470_590.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___470_590.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___470_590.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___470_590.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___470_590.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___470_590.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___470_590.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___470_590.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___470_590.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___470_590.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___470_590.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___470_590.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___470_590.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___470_590.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___470_590.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___470_590.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___470_590.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___470_590.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___470_590.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___470_590.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___470_590.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___470_590.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___470_590.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___470_590.FStar_TypeChecker_Env.nbe)
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
          let uu____625 =
            let uu____627 =
              let uu____629 = FStar_Options.file_list ()  in
              FStar_List.hd uu____629  in
            FStar_Parser_Dep.lowercase_module_name uu____627  in
          let uu____634 =
            let uu____636 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____636  in
          uu____625 = uu____634  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____645,{ FStar_Parser_AST.d = uu____646;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____648;
                           FStar_Parser_AST.quals = uu____649;
                           FStar_Parser_AST.attrs = uu____650;_}::uu____651)
              -> d
          | FStar_Parser_AST.Interface
              (uu____658,{ FStar_Parser_AST.d = uu____659;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____661;
                           FStar_Parser_AST.quals = uu____662;
                           FStar_Parser_AST.attrs = uu____663;_}::uu____664,uu____665)
              -> d
          | uu____674 -> FStar_Range.dummyRange  in
        let uu____675 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____675 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____687 =
              let uu____692 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____692  in
            (match uu____687 with
             | (ast_modul1,env1) ->
                 let uu____717 =
                   let uu____722 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____722
                    in
                 (match uu____717 with
                  | (modul,env2) ->
                      ((let uu____747 =
                          let uu____749 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____749  in
                        if uu____747
                        then
                          let msg =
                            let uu____754 =
                              let uu____756 =
                                let uu____758 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____758  in
                              FStar_Parser_Dep.module_name_of_file uu____756
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____754
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____767 =
                          let uu____778 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____778
                          then ((modul, []), env2)
                          else
                            (let uu____801 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____801 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____767 with
                        | ((modul1,uu____842),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____865 = FStar_List.hd ast_decls  in
                 (match uu____865 with
                  | { FStar_Parser_AST.d = uu____872;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____874;
                      FStar_Parser_AST.quals = uu____875;
                      FStar_Parser_AST.attrs = uu____876;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____888 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____906 =
                            let uu____913 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____913
                             in
                          match uu____906 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____888 with
                  | (env1,ast_decls_l) ->
                      let uu____967 =
                        let uu____972 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____972
                         in
                      (match uu____967 with
                       | (sigelts,env2) ->
                           let uu____996 =
                             let uu____1005 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____1005
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____996 with
                            | (modul1,uu____1027,env3) ->
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
           (l,decls,uu____1051)),uu____1052)
          ->
          let uu____1075 =
            let uu____1080 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____1080  in
          FStar_Pervasives_Native.snd uu____1075
      | FStar_Parser_ParseIt.ASTFragment uu____1096 ->
          let uu____1108 =
            let uu____1114 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____1114)  in
          FStar_Errors.raise_err uu____1108
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____1124 ->
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
    let uu____1221 = FStar_Util.load_value_from_file cache_file  in
    match uu____1221 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inl "Corrupt"
    | FStar_Pervasives_Native.Some (vnum,digest,tc_result) ->
        if vnum <> cache_version_number
        then FStar_Util.Inl "Stale, because inconsistent cache version"
        else
          (let uu____1323 =
             let uu____1334 = FStar_TypeChecker_Env.dep_graph env  in
             FStar_Parser_Dep.hash_dependences uu____1334 source_file
               cache_file
              in
           match uu____1323 with
           | FStar_Pervasives_Native.Some digest' ->
               if digest = digest'
               then FStar_Util.Inr tc_result
               else
                 ((let uu____1375 = FStar_Options.debug_any ()  in
                   if uu____1375
                   then
                     ((let uu____1379 =
                         FStar_Util.string_of_int (FStar_List.length digest')
                          in
                       let uu____1387 = FStar_Parser_Dep.print_digest digest'
                          in
                       let uu____1389 =
                         FStar_Util.string_of_int (FStar_List.length digest)
                          in
                       let uu____1397 = FStar_Parser_Dep.print_digest digest
                          in
                       FStar_Util.print4
                         "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                         uu____1379 uu____1387 uu____1389 uu____1397);
                      if
                        (FStar_List.length digest) =
                          (FStar_List.length digest')
                      then
                        FStar_List.iter2
                          (fun uu____1433  ->
                             fun uu____1434  ->
                               match (uu____1433, uu____1434) with
                               | ((x,y),(x',y')) ->
                                   if (x <> x') || (y <> y')
                                   then
                                     let uu____1486 =
                                       FStar_Parser_Dep.print_digest [(x, y)]
                                        in
                                     let uu____1502 =
                                       FStar_Parser_Dep.print_digest
                                         [(x', y')]
                                        in
                                     FStar_Util.print2
                                       "Differ at: Expected %s\n Got %s\n"
                                       uu____1486 uu____1502
                                   else ()) digest digest'
                      else ())
                   else ());
                  FStar_Util.Inl "Stale")
           | uu____1527 -> FStar_Util.Inl "Unable to compute digest of")
     in
  fun env  ->
    fun fn  ->
      let load_it uu____1550 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn  in
        let fail1 maybe_warn cache_file1 =
          invalidate_cache ();
          (match maybe_warn with
           | FStar_Pervasives_Native.None  -> ()
           | FStar_Pervasives_Native.Some tag ->
               let uu____1577 =
                 let uu____1578 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 let uu____1581 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 FStar_Range.mk_range fn uu____1578 uu____1581  in
               let uu____1584 =
                 let uu____1590 =
                   FStar_Util.format3
                     "%s cache file %s; will recheck %s and all subsequent files"
                     tag cache_file1 fn
                    in
                 (FStar_Errors.Warning_CachedFile, uu____1590)  in
               FStar_Errors.log_issue uu____1577 uu____1584)
           in
        let uu____1594 = FStar_ST.op_Bang some_cache_invalid  in
        match uu____1594 with
        | FStar_Pervasives_Native.Some uu____1644 ->
            FStar_Pervasives_Native.None
        | uu____1645 ->
            if Prims.op_Negation (FStar_Util.file_exists cache_file)
            then FStar_Pervasives_Native.None
            else
              (let uu____1653 =
                 load1 env.FStar_Extraction_ML_UEnv.env_tcenv fn cache_file
                  in
               match uu____1653 with
               | FStar_Util.Inl msg ->
                   (fail1 (FStar_Pervasives_Native.Some msg) cache_file;
                    FStar_Pervasives_Native.None)
               | FStar_Util.Inr res -> FStar_Pervasives_Native.Some res)
         in
      FStar_Options.profile load_it
        (fun res  ->
           let msg = if FStar_Option.isSome res then "ok" else "failed"  in
           let uu____1684 = FStar_Parser_Dep.cache_file_name fn  in
           FStar_Util.format2 "Loading checked file %s ... %s" uu____1684 msg)
  
let (store_module_to_cache : uenv -> Prims.string -> tc_result -> unit) =
  fun env  ->
    fun fn  ->
      fun tc_result  ->
        let uu____1705 =
          (FStar_Options.cache_checked_modules ()) &&
            (let uu____1708 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____1708)
           in
        if uu____1705
        then
          let cache_file = FStar_Parser_Dep.cache_file_name fn  in
          let digest =
            let uu____1724 =
              FStar_TypeChecker_Env.dep_graph
                env.FStar_Extraction_ML_UEnv.env_tcenv
               in
            FStar_Parser_Dep.hash_dependences uu____1724 fn cache_file  in
          match digest with
          | FStar_Pervasives_Native.Some hashes ->
              let tc_result1 =
                let uu___471_1743 = tc_result  in
                {
                  checked_module = (uu___471_1743.checked_module);
                  mii = (uu___471_1743.mii);
                  smt_decls = (uu___471_1743.smt_decls);
                  tc_time = (Prims.parse_int "0");
                  extraction_time = (uu___471_1743.extraction_time)
                }  in
              FStar_Util.save_value_to_file cache_file
                (cache_version_number, hashes, tc_result1)
          | uu____1769 ->
              let uu____1780 =
                let uu____1781 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                let uu____1784 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range fn uu____1781 uu____1784  in
              let uu____1787 =
                let uu____1793 =
                  FStar_Util.format1
                    "%s was not written, since some of its dependences were not also checked"
                    cache_file
                   in
                (FStar_Errors.Warning_FileNotWritten, uu____1793)  in
              FStar_Errors.log_issue uu____1780 uu____1787
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
            ((fun e  -> let uu____1877 = f1 e  in g uu____1877))
  
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
        | uu____1901 -> failwith "Unrecognized option"  in
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
           | (name,uu____1926)::[] ->
               let uu____1929 =
                 FStar_Options.prepend_output_dir (Prims.strcat name ext)  in
               FStar_Util.save_value_to_file uu____1929 bin
           | uu____1931 ->
               let uu____1934 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____1934 bin)
      | uu____1937 -> failwith "Unrecognized option"
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
             let uu____2013 =
               (let uu____2017 = FStar_Options.codegen ()  in
                uu____2017 = FStar_Pervasives_Native.None) ||
                 (let uu____2023 =
                    FStar_Options.should_extract
                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  Prims.op_Negation uu____2023)
                in
             if uu____2013
             then (FStar_Pervasives_Native.None, (Prims.parse_int "0"))
             else
               FStar_Util.record_time
                 (fun uu____2045  ->
                    let uu____2046 =
                      FStar_Extraction_ML_Modul.extract env1 tcmod  in
                    match uu____2046 with | (uu____2055,defs) -> defs)
              in
           let maybe_extract_ml_iface tcmod env1 =
             let uu____2077 =
               let uu____2079 = FStar_Options.codegen ()  in
               uu____2079 = FStar_Pervasives_Native.None  in
             if uu____2077
             then (env1, (Prims.parse_int "0"))
             else
               (let uu____2094 =
                  FStar_Util.record_time
                    (fun uu____2109  ->
                       FStar_Extraction_ML_Modul.extract_iface env1 tcmod)
                   in
                match uu____2094 with
                | ((env2,_extracted_iface),iface_extract_time) ->
                    (env2, iface_extract_time))
              in
           let tc_source_file uu____2138 =
             let env1 = apply_delta_env env delta1  in
             let uu____2142 = parse env1 pre_fn fn  in
             match uu____2142 with
             | (fmod,env2) ->
                 let mii =
                   FStar_Syntax_DsEnv.inclusion_info
                     (env2.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                     fmod.FStar_Syntax_Syntax.name
                    in
                 let check_mod uu____2171 =
                   let uu____2172 =
                     FStar_Util.record_time
                       (fun uu____2207  ->
                          with_tcenv_of_env env2
                            (fun tcenv  ->
                               (match tcenv.FStar_TypeChecker_Env.gamma with
                                | [] -> ()
                                | uu____2226 ->
                                    failwith
                                      "Impossible: gamma contains leaked names");
                               (let uu____2230 =
                                  FStar_TypeChecker_Tc.check_module tcenv
                                    fmod (FStar_Util.is_some pre_fn)
                                   in
                                match uu____2230 with
                                | (modul,env3) ->
                                    let smt_decls =
                                      let uu____2259 =
                                        let uu____2261 = FStar_Options.lax ()
                                           in
                                        Prims.op_Negation uu____2261  in
                                      if uu____2259
                                      then
                                        let smt_decls =
                                          FStar_SMTEncoding_Encode.encode_modul
                                            env3 modul
                                           in
                                        (FStar_SMTEncoding_Z3.refresh ();
                                         smt_decls)
                                      else ([], [])  in
                                    ((modul, smt_decls), env3))))
                      in
                   match uu____2172 with
                   | (((tcmod,smt_decls),env3),tc_time) ->
                       let uu____2348 =
                         with_env env3 (maybe_extract_mldefs tcmod)  in
                       (match uu____2348 with
                        | (extracted_defs,extract_time) ->
                            let uu____2379 =
                              with_env env3 (maybe_extract_ml_iface tcmod)
                               in
                            (match uu____2379 with
                             | (env4,iface_extraction_time) ->
                                 ({
                                    checked_module = tcmod;
                                    mii;
                                    smt_decls;
                                    tc_time;
                                    extraction_time =
                                      (extract_time + iface_extraction_time)
                                  }, extracted_defs, env4)))
                    in
                 let uu____2404 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                    in
                 if uu____2404
                 then
                   let uu____2415 = FStar_Parser_ParseIt.find_file fn  in
                   FStar_SMTEncoding_Solver.with_hints_db uu____2415
                     check_mod
                 else check_mod ()
              in
           let uu____2427 =
             let uu____2429 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____2429  in
           if uu____2427
           then
             let uu____2442 = load_module_from_cache env fn  in
             match uu____2442 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____2456 =
                     let uu____2458 = FStar_Parser_Dep.module_name_of_file fn
                        in
                     FStar_Options.should_be_already_cached uu____2458  in
                   if uu____2456
                   then
                     let uu____2461 =
                       let uu____2467 =
                         FStar_Util.format1
                           "Expected %s to already be checked" fn
                          in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____2467)
                        in
                     FStar_Errors.raise_err uu____2461
                   else ());
                  (let uu____2474 =
                     (let uu____2478 = FStar_Options.codegen ()  in
                      FStar_Option.isSome uu____2478) &&
                       (FStar_Options.cmi ())
                      in
                   if uu____2474
                   then
                     let uu____2482 =
                       let uu____2488 =
                         FStar_Util.format1
                           "Cross-module inlining expects all modules to be checked first; %s was not checked"
                           fn
                          in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu____2488)
                        in
                     FStar_Errors.raise_err uu____2482
                   else ());
                  (let uu____2494 = tc_source_file ()  in
                   match uu____2494 with
                   | (tc_result,mllib,env1) ->
                       ((let uu____2521 =
                           (let uu____2525 = FStar_Errors.get_err_count ()
                               in
                            uu____2525 = (Prims.parse_int "0")) &&
                             ((FStar_Options.lax ()) ||
                                (FStar_Options.should_verify
                                   ((tc_result.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                            in
                         if uu____2521
                         then store_module_to_cache env1 fn tc_result
                         else ());
                        (tc_result, mllib, env1,
                          FStar_Pervasives_Native.None))))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.checked_module  in
                 let smt_decls = tc_result.smt_decls  in
                 ((let uu____2547 =
                     FStar_Options.dump_module
                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____2547
                   then
                     let uu____2550 =
                       FStar_Syntax_Print.modul_to_string tcmod  in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____2550
                   else ());
                  (let delta_tcenv tcmod1 tcenv =
                     let uu____2570 =
                       let uu____2575 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                           tc_result.mii
                           (FStar_TypeChecker_Normalize.erase_universes tcenv)
                          in
                       FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                         uu____2575
                        in
                     match uu____2570 with
                     | (uu____2595,tcenv1) ->
                         let env1 =
                           FStar_TypeChecker_Tc.load_checked_module tcenv1
                             tcmod1
                            in
                         ((let uu____2599 =
                             let uu____2601 = FStar_Options.lax ()  in
                             Prims.op_Negation uu____2601  in
                           if uu____2599
                           then
                             (FStar_SMTEncoding_Encode.encode_modul_from_cache
                                env1 tcmod1.FStar_Syntax_Syntax.name
                                smt_decls;
                              FStar_SMTEncoding_Z3.refresh ())
                           else ());
                          ((), env1))
                      in
                   let mllib =
                     let uu____2610 =
                       ((let uu____2614 = FStar_Options.codegen ()  in
                         uu____2614 <> FStar_Pervasives_Native.None) &&
                          (FStar_Options.should_extract
                             (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                         &&
                         ((Prims.op_Negation
                             tcmod.FStar_Syntax_Syntax.is_interface)
                            ||
                            (let uu____2620 = FStar_Options.codegen ()  in
                             uu____2620 =
                               (FStar_Pervasives_Native.Some
                                  FStar_Options.Kremlin)))
                        in
                     if uu____2610
                     then
                       with_env env
                         (fun env1  ->
                            let env2 = apply_delta_env env1 delta1  in
                            let extract_defs tcmod1 env3 =
                              let uu____2658 =
                                with_tcenv_of_env env3 (delta_tcenv tcmod1)
                                 in
                              match uu____2658 with
                              | (uu____2670,env4) ->
                                  maybe_extract_mldefs tcmod1 env4
                               in
                            let uu____2672 = extract_defs tcmod env2  in
                            match uu____2672 with
                            | (extracted_defs,extraction_time) ->
                                extracted_defs)
                     else FStar_Pervasives_Native.None  in
                   let delta_env env1 =
                     FStar_Options.profile
                       (fun uu____2705  ->
                          let uu____2706 =
                            with_tcenv_of_env env1 (delta_tcenv tcmod)  in
                          match uu____2706 with
                          | (uu____2711,env2) ->
                              let uu____2713 =
                                with_env env2 (maybe_extract_ml_iface tcmod)
                                 in
                              (match uu____2713 with | (env3,_time) -> env3))
                       (fun uu____2729  ->
                          FStar_Util.format1
                            "Extending environment with module %s"
                            (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                      in
                   (tc_result, mllib, env,
                     (extend_delta_env delta1 delta_env))))
           else
             (let uu____2738 = tc_source_file ()  in
              match uu____2738 with
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
        let uu____2802 =
          tc_one_file env1 FStar_Pervasives_Native.None pre_fn fn  in
        match uu____2802 with
        | (tc_result,uu____2821,env2,delta1) ->
            let uu____2828 =
              let uu____2829 = apply_delta_env env2 delta1  in
              uu____2829.FStar_Extraction_ML_UEnv.env_tcenv  in
            (tc_result, uu____2828)
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____2854 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____2854 ["fsti"; "fsi"]))
        &&
        (let uu____2863 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____2863 ["fst"; "fs"])
  
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
        let uu____2912 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____2961 =
                tc_one_file env delta_env (FStar_Pervasives_Native.Some intf)
                  impl
                 in
              (match uu____2961 with
               | (m,mllib,env1,delta_env1) ->
                   (remaining1, ([m], mllib, env1, delta_env1)))
          | intf_or_impl::remaining1 ->
              let uu____3030 =
                tc_one_file env delta_env FStar_Pervasives_Native.None
                  intf_or_impl
                 in
              (match uu____3030 with
               | (m,mllib,env1,delta_env1) ->
                   (remaining1, ([m], mllib, env1, delta_env1)))
          | [] -> ([], ([], FStar_Pervasives_Native.None, env, delta_env))
           in
        match uu____2912 with
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
      let as_list uu___462_3234 =
        match uu___462_3234 with
        | FStar_Pervasives_Native.None  -> []
        | FStar_Pervasives_Native.Some l -> [l]  in
      match remaining with
      | [] -> acc
      | uu____3253 ->
          let uu____3257 = acc  in
          (match uu____3257 with
           | (mods,mllibs,env,delta_env) ->
               let uu____3294 =
                 tc_one_file_from_remaining remaining env delta_env  in
               (match uu____3294 with
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
      (let uu____3382 = FStar_Options.debug_any ()  in
       if uu____3382
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____3390 =
             let uu____3392 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____3392  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____3390))
       else ());
      (let env =
         let uu____3408 = init_env dep_graph1  in
         FStar_Extraction_ML_UEnv.mkContext uu____3408  in
       let uu____3409 =
         tc_fold_interleave ([], [], env, FStar_Pervasives_Native.None)
           filenames
          in
       match uu____3409 with
       | (all_mods,mllibs,env1,delta1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____3461 =
                 with_tcenv_of_env env2
                   (fun tcenv  ->
                      (let uu____3470 =
                         (FStar_Options.interactive ()) &&
                           (let uu____3473 = FStar_Errors.get_err_count ()
                               in
                            uu____3473 = (Prims.parse_int "0"))
                          in
                       if uu____3470
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv))
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____3461  in
             (all_mods, env1, (extend_delta_env delta1 solver_refresh)))))
  