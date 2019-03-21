open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "9") 
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
      let uu____71099 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____71099 with
      | (a,dsenv1) ->
          (a,
            (let uu___713_71111 = tcenv  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___713_71111.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___713_71111.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___713_71111.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___713_71111.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___713_71111.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___713_71111.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___713_71111.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___713_71111.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___713_71111.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___713_71111.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___713_71111.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___713_71111.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___713_71111.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___713_71111.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___713_71111.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___713_71111.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___713_71111.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___713_71111.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___713_71111.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___713_71111.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___713_71111.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___713_71111.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___713_71111.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___713_71111.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___713_71111.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___713_71111.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___713_71111.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___713_71111.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___713_71111.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___713_71111.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___713_71111.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___713_71111.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___713_71111.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___713_71111.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___713_71111.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___713_71111.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___713_71111.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___713_71111.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___713_71111.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___713_71111.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___713_71111.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___713_71111.FStar_TypeChecker_Env.nbe)
             }))
  
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e  ->
    fun f  ->
      let uu____71147 = f e.FStar_Extraction_ML_UEnv.env_tcenv  in
      match uu____71147 with
      | (a,t') ->
          (a,
            (let uu___721_71159 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___721_71159.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___721_71159.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___721_71159.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___721_71159.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e  ->
    fun f  ->
      let uu____71188 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f  in
      match uu____71188 with
      | (a,tcenv) ->
          (a,
            (let uu___729_71200 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___729_71200.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___729_71200.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___729_71200.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___729_71200.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____71207 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____71215 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env"
              in
           ((), uu____71215))
       in
    FStar_Pervasives_Native.snd uu____71207
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____71223 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____71231 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____71231))
       in
    FStar_Pervasives_Native.snd uu____71223
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____71258 = pop_env env1  in res
  
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
        let uu____71297 = FStar_Parser_Driver.parse_file fn  in
        match uu____71297 with
        | (ast,uu____71314) ->
            let uu____71329 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____71342 = FStar_Parser_Driver.parse_file pre_fn1
                     in
                  (match uu____71342 with
                   | (pre_ast,uu____71359) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____71380),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____71393 =
                              let uu____71398 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____71398  in
                            (match uu____71393 with
                             | (uu____71407,env1) ->
                                 let uu____71409 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____71409)
                        | uu____71415 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____71329 with
             | (ast1,env1) ->
                 let uu____71432 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____71432)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____71444 = FStar_Options.lax ()  in
      if uu____71444
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___773_71449 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___773_71449.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___773_71449.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___773_71449.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___773_71449.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___773_71449.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_sig =
             (uu___773_71449.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___773_71449.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___773_71449.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___773_71449.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____71451 =
        let uu____71466 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____71466  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____71451
       in
    let env1 =
      let uu___777_71470 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___777_71470.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___777_71470.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___777_71470.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___777_71470.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___777_71470.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___777_71470.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___777_71470.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___777_71470.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___777_71470.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___777_71470.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___777_71470.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___777_71470.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___777_71470.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___777_71470.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___777_71470.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___777_71470.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___777_71470.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___777_71470.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___777_71470.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___777_71470.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___777_71470.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___777_71470.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___777_71470.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___777_71470.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___777_71470.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___777_71470.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___777_71470.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___777_71470.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___777_71470.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___777_71470.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___777_71470.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___777_71470.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___777_71470.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___777_71470.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___777_71470.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___777_71470.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___777_71470.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___777_71470.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___777_71470.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___777_71470.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___777_71470.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___777_71470.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___780_71472 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___780_71472.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___780_71472.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___780_71472.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___780_71472.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___780_71472.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___780_71472.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___780_71472.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___780_71472.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___780_71472.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___780_71472.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___780_71472.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___780_71472.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___780_71472.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___780_71472.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___780_71472.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___780_71472.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___780_71472.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___780_71472.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___780_71472.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___780_71472.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___780_71472.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___780_71472.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___780_71472.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___780_71472.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___780_71472.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___780_71472.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___780_71472.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___780_71472.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___780_71472.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___780_71472.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___780_71472.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___780_71472.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___780_71472.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___780_71472.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___780_71472.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___780_71472.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___780_71472.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___780_71472.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___780_71472.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___780_71472.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___780_71472.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___780_71472.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___783_71474 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___783_71474.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___783_71474.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___783_71474.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___783_71474.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___783_71474.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___783_71474.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___783_71474.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___783_71474.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___783_71474.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___783_71474.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___783_71474.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___783_71474.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___783_71474.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___783_71474.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___783_71474.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___783_71474.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___783_71474.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___783_71474.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___783_71474.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___783_71474.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___783_71474.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___783_71474.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___783_71474.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___783_71474.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___783_71474.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___783_71474.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___783_71474.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___783_71474.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___783_71474.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___783_71474.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___783_71474.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___783_71474.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___783_71474.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___783_71474.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___783_71474.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___783_71474.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___783_71474.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___783_71474.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___783_71474.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___783_71474.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___783_71474.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___783_71474.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___786_71476 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___786_71476.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___786_71476.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___786_71476.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___786_71476.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___786_71476.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___786_71476.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___786_71476.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___786_71476.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___786_71476.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___786_71476.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___786_71476.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___786_71476.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___786_71476.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___786_71476.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___786_71476.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___786_71476.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___786_71476.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___786_71476.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___786_71476.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___786_71476.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___786_71476.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___786_71476.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___786_71476.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___786_71476.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___786_71476.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___786_71476.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___786_71476.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___786_71476.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___786_71476.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___786_71476.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___786_71476.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___786_71476.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___786_71476.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___786_71476.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___786_71476.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___786_71476.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___786_71476.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___786_71476.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___786_71476.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___786_71476.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___786_71476.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___786_71476.FStar_TypeChecker_Env.nbe)
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
          let uu____71511 =
            let uu____71513 =
              let uu____71515 = FStar_Options.file_list ()  in
              FStar_List.hd uu____71515  in
            FStar_Parser_Dep.lowercase_module_name uu____71513  in
          let uu____71520 =
            let uu____71522 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____71522  in
          uu____71511 = uu____71520  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____71531,{ FStar_Parser_AST.d = uu____71532;
                             FStar_Parser_AST.drange = d;
                             FStar_Parser_AST.doc = uu____71534;
                             FStar_Parser_AST.quals = uu____71535;
                             FStar_Parser_AST.attrs = uu____71536;_}::uu____71537)
              -> d
          | FStar_Parser_AST.Interface
              (uu____71544,{ FStar_Parser_AST.d = uu____71545;
                             FStar_Parser_AST.drange = d;
                             FStar_Parser_AST.doc = uu____71547;
                             FStar_Parser_AST.quals = uu____71548;
                             FStar_Parser_AST.attrs = uu____71549;_}::uu____71550,uu____71551)
              -> d
          | uu____71560 -> FStar_Range.dummyRange  in
        let uu____71561 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____71561 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____71573 =
              let uu____71578 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____71578  in
            (match uu____71573 with
             | (ast_modul1,env1) ->
                 let uu____71599 =
                   let uu____71604 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____71604
                    in
                 (match uu____71599 with
                  | (modul,env2) ->
                      ((let uu____71625 =
                          let uu____71627 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____71627  in
                        if uu____71625
                        then
                          let msg =
                            let uu____71632 =
                              let uu____71634 =
                                let uu____71636 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____71636  in
                              FStar_Parser_Dep.module_name_of_file
                                uu____71634
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____71632
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____71645 =
                          let uu____71656 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____71656
                          then ((modul, []), env2)
                          else
                            (let uu____71679 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____71679 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____71645 with
                        | ((modul1,uu____71720),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____71743 = FStar_List.hd ast_decls  in
                 (match uu____71743 with
                  | { FStar_Parser_AST.d = uu____71750;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____71752;
                      FStar_Parser_AST.quals = uu____71753;
                      FStar_Parser_AST.attrs = uu____71754;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____71766 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____71784 =
                            let uu____71791 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____71791
                             in
                          match uu____71784 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____71766 with
                  | (env1,ast_decls_l) ->
                      let uu____71841 =
                        let uu____71846 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____71846
                         in
                      (match uu____71841 with
                       | (sigelts,env2) ->
                           let uu____71866 =
                             let uu____71875 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____71875
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____71866 with
                            | (modul1,uu____71897,env3) ->
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
           (l,decls,uu____71921)),uu____71922)
          ->
          let uu____71945 =
            let uu____71950 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____71950  in
          FStar_Pervasives_Native.snd uu____71945
      | FStar_Parser_ParseIt.ASTFragment uu____71962 ->
          let uu____71974 =
            let uu____71980 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____71980)  in
          FStar_Errors.raise_err uu____71974
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____71990 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
  
type cache_t =
  (Prims.int * (Prims.string * Prims.string) Prims.list * Prims.string *
    FStar_Parser_Dep.parsing_data * tc_result)
let (load_value_from_cache :
  Prims.string -> (cache_t FStar_Pervasives_Native.option * Prims.string)) =
  fun cache_file  ->
    let uu____72034 = FStar_Util.load_value_from_file cache_file  in
    match uu____72034 with
    | FStar_Pervasives_Native.None  ->
        (FStar_Pervasives_Native.None, "Corrupt")
    | FStar_Pervasives_Native.Some cache_data ->
        let uu____72149 = cache_data  in
        (match uu____72149 with
         | (vnum,uu____72178,uu____72179,uu____72180,uu____72181) ->
             if vnum <> cache_version_number
             then
               (FStar_Pervasives_Native.None,
                 "Stale, because inconsistent cache version")
             else ((FStar_Pervasives_Native.Some cache_data), ""))
  
let (store_value_to_cache : Prims.string -> cache_t -> unit) =
  fun cache_file  ->
    fun data  -> FStar_Util.save_value_to_file cache_file data
  
let (load_parsing_data_from_cache :
  Prims.string ->
    FStar_Parser_Dep.parsing_data FStar_Pervasives_Native.option)
  =
  fun file_name  ->
    let cache_file =
      try
        (fun uu___907_72255  ->
           match () with
           | () ->
               let uu____72259 = FStar_Parser_Dep.cache_file_name file_name
                  in
               FStar_All.pipe_right uu____72259
                 (fun _72266  -> FStar_Pervasives_Native.Some _72266)) ()
      with | uu___906_72268 -> FStar_Pervasives_Native.None  in
    if cache_file = FStar_Pervasives_Native.None
    then FStar_Pervasives_Native.None
    else
      (let uu____72282 =
         let uu____72310 = FStar_All.pipe_right cache_file FStar_Util.must
            in
         FStar_All.pipe_right uu____72310 load_value_from_cache  in
       match uu____72282 with
       | (FStar_Pervasives_Native.None ,uu____72347) ->
           FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.Some
          (uu____72392,uu____72393,dig,pd,uu____72396),uu____72397) ->
           let uu____72462 =
             let uu____72464 = FStar_Util.digest_of_file file_name  in
             dig <> uu____72464  in
           if uu____72462
           then FStar_Pervasives_Native.None
           else FStar_Pervasives_Native.Some pd)
  
let (load_module_from_cache :
  uenv -> Prims.string -> tc_result FStar_Pervasives_Native.option) =
  let some_cache_invalid = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let invalidate_cache fn =
    FStar_ST.op_Colon_Equals some_cache_invalid
      (FStar_Pervasives_Native.Some ())
     in
  let load1 env source_file cache_file =
    let uu____72545 = load_value_from_cache cache_file  in
    match uu____72545 with
    | (FStar_Pervasives_Native.None ,msg) -> FStar_Util.Inl msg
    | (FStar_Pervasives_Native.Some
       (uu____72564,digest,uu____72566,uu____72567,tc_result),uu____72569) ->
        let uu____72594 =
          let uu____72608 = FStar_TypeChecker_Env.dep_graph env  in
          FStar_Parser_Dep.hash_dependences uu____72608 source_file
            cache_file
           in
        (match uu____72594 with
         | FStar_Util.Inr digest' ->
             if digest = digest'
             then FStar_Util.Inr tc_result
             else
               ((let uu____72650 = FStar_Options.debug_any ()  in
                 if uu____72650
                 then
                   ((let uu____72654 =
                       FStar_Util.string_of_int (FStar_List.length digest')
                        in
                     let uu____72662 = FStar_Parser_Dep.print_digest digest'
                        in
                     let uu____72664 =
                       FStar_Util.string_of_int (FStar_List.length digest)
                        in
                     let uu____72672 = FStar_Parser_Dep.print_digest digest
                        in
                     FStar_Util.print4
                       "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                       uu____72654 uu____72662 uu____72664 uu____72672);
                    if
                      (FStar_List.length digest) =
                        (FStar_List.length digest')
                    then
                      FStar_List.iter2
                        (fun uu____72708  ->
                           fun uu____72709  ->
                             match (uu____72708, uu____72709) with
                             | ((x,y),(x',y')) ->
                                 if (x <> x') || (y <> y')
                                 then
                                   let uu____72761 =
                                     FStar_Parser_Dep.print_digest [(x, y)]
                                      in
                                   let uu____72777 =
                                     FStar_Parser_Dep.print_digest [(x', y')]
                                      in
                                   FStar_Util.print2
                                     "Differ at: Expected %s\n Got %s\n"
                                     uu____72761 uu____72777
                                 else ()) digest digest'
                    else ())
                 else ());
                FStar_Util.Inl "Stale")
         | FStar_Util.Inl msg -> FStar_Util.Inl msg)
     in
  fun env  ->
    fun fn  ->
      let load_it uu____72824 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn  in
        let fail1 msg cache_file1 =
          invalidate_cache ();
          (let uu____72843 =
             let uu____72845 = FStar_Options.should_verify_file fn  in
             Prims.op_Negation uu____72845  in
           if uu____72843
           then
             let uu____72848 =
               let uu____72849 =
                 FStar_Range.mk_pos (Prims.parse_int "0")
                   (Prims.parse_int "0")
                  in
               let uu____72852 =
                 FStar_Range.mk_pos (Prims.parse_int "0")
                   (Prims.parse_int "0")
                  in
               FStar_Range.mk_range fn uu____72849 uu____72852  in
             let uu____72855 =
               let uu____72861 =
                 FStar_Util.format3
                   "Unable to compute digest of %s since %s; will recheck %s and all subsequent files"
                   cache_file1 msg fn
                  in
               (FStar_Errors.Warning_CachedFile, uu____72861)  in
             FStar_Errors.log_issue uu____72848 uu____72855
           else ())
           in
        let uu____72867 = FStar_ST.op_Bang some_cache_invalid  in
        match uu____72867 with
        | FStar_Pervasives_Native.Some uu____72895 ->
            FStar_Pervasives_Native.None
        | uu____72896 ->
            if Prims.op_Negation (FStar_Util.file_exists cache_file)
            then
              ((let uu____72903 =
                  FStar_Util.format1 "file %s does not exists" cache_file  in
                fail1 uu____72903 cache_file);
               FStar_Pervasives_Native.None)
            else
              (let uu____72908 =
                 load1 env.FStar_Extraction_ML_UEnv.env_tcenv fn cache_file
                  in
               match uu____72908 with
               | FStar_Util.Inl msg ->
                   (fail1 msg cache_file; FStar_Pervasives_Native.None)
               | FStar_Util.Inr res -> FStar_Pervasives_Native.Some res)
         in
      FStar_Options.profile load_it
        (fun res  ->
           let msg = if FStar_Option.isSome res then "ok" else "failed"  in
           let uu____72938 = FStar_Parser_Dep.cache_file_name fn  in
           FStar_Util.format2 "Loading checked file %s ... %s" uu____72938
             msg)
  
let (store_module_to_cache :
  uenv -> Prims.string -> FStar_Parser_Dep.parsing_data -> tc_result -> unit)
  =
  fun env  ->
    fun fn  ->
      fun parsing_data  ->
        fun tc_result  ->
          let uu____72964 =
            (FStar_Options.cache_checked_modules ()) &&
              (let uu____72967 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____72967)
             in
          if uu____72964
          then
            let cache_file = FStar_Parser_Dep.cache_file_name fn  in
            let digest =
              let uu____72986 =
                FStar_TypeChecker_Env.dep_graph
                  env.FStar_Extraction_ML_UEnv.env_tcenv
                 in
              FStar_Parser_Dep.hash_dependences uu____72986 fn cache_file  in
            match digest with
            | FStar_Util.Inr hashes ->
                let tc_result1 =
                  let uu___994_73006 = tc_result  in
                  {
                    checked_module = (uu___994_73006.checked_module);
                    mii = (uu___994_73006.mii);
                    smt_decls = (uu___994_73006.smt_decls);
                    tc_time = (Prims.parse_int "0");
                    extraction_time = (uu___994_73006.extraction_time)
                  }  in
                let uu____73008 =
                  let uu____73009 = FStar_Util.digest_of_file fn  in
                  (cache_version_number, hashes, uu____73009, parsing_data,
                    tc_result1)
                   in
                store_value_to_cache cache_file uu____73008
            | FStar_Util.Inl msg ->
                let uu____73032 =
                  let uu____73033 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  let uu____73036 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  FStar_Range.mk_range fn uu____73033 uu____73036  in
                let uu____73039 =
                  let uu____73045 =
                    FStar_Util.format2
                      "%s was not written, since some of its dependences were not also checked: %s"
                      cache_file msg
                     in
                  (FStar_Errors.Warning_FileNotWritten, uu____73045)  in
                FStar_Errors.log_issue uu____73032 uu____73039
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
            ((fun e  -> let uu____73122 = f1 e  in g uu____73122))
  
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
        | uu____73146 -> failwith "Unrecognized option"  in
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
           | (name,uu____73171)::[] ->
               let uu____73174 =
                 FStar_Options.prepend_output_dir (Prims.op_Hat name ext)  in
               FStar_Util.save_value_to_file uu____73174 bin
           | uu____73176 ->
               let uu____73179 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____73179 bin)
      | uu____73182 -> failwith "Unrecognized option"
    else ()
  
let (tc_one_file :
  uenv ->
    delta_env ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          FStar_Parser_Dep.parsing_data ->
            (tc_result * FStar_Extraction_ML_Syntax.mllib
              FStar_Pervasives_Native.option * uenv * delta_env))
  =
  fun env  ->
    fun delta1  ->
      fun pre_fn  ->
        fun fn  ->
          fun parsing_data  ->
            FStar_Ident.reset_gensym ();
            (let post_smt_encoding uu____73248 =
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____73250 =
                  let uu____73252 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____73252  in
                if uu____73250
                then
                  let uu____73255 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____73255 (fun a1  -> ())
                else ())
                in
             let maybe_extract_mldefs tcmod env1 =
               let uu____73277 =
                 (let uu____73281 = FStar_Options.codegen ()  in
                  uu____73281 = FStar_Pervasives_Native.None) ||
                   (let uu____73287 =
                      FStar_Options.should_extract
                        (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    Prims.op_Negation uu____73287)
                  in
               if uu____73277
               then (FStar_Pervasives_Native.None, (Prims.parse_int "0"))
               else
                 FStar_Util.record_time
                   (fun uu____73309  ->
                      let uu____73310 =
                        FStar_Extraction_ML_Modul.extract env1 tcmod  in
                      match uu____73310 with | (uu____73319,defs) -> defs)
                in
             let maybe_extract_ml_iface tcmod env1 =
               let uu____73341 =
                 let uu____73343 = FStar_Options.codegen ()  in
                 uu____73343 = FStar_Pervasives_Native.None  in
               if uu____73341
               then (env1, (Prims.parse_int "0"))
               else
                 (let uu____73358 =
                    FStar_Util.record_time
                      (fun uu____73373  ->
                         FStar_Extraction_ML_Modul.extract_iface env1 tcmod)
                     in
                  match uu____73358 with
                  | ((env2,_extracted_iface),iface_extract_time) ->
                      (env2, iface_extract_time))
                in
             let tc_source_file uu____73402 =
               let env1 = apply_delta_env env delta1  in
               let uu____73404 = parse env1 pre_fn fn  in
               match uu____73404 with
               | (fmod,env2) ->
                   let mii =
                     FStar_Syntax_DsEnv.inclusion_info
                       (env2.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                       fmod.FStar_Syntax_Syntax.name
                      in
                   let check_mod uu____73433 =
                     let uu____73434 =
                       FStar_Util.record_time
                         (fun uu____73469  ->
                            with_tcenv_of_env env2
                              (fun tcenv  ->
                                 (match tcenv.FStar_TypeChecker_Env.gamma
                                  with
                                  | [] -> ()
                                  | uu____73488 ->
                                      failwith
                                        "Impossible: gamma contains leaked names");
                                 (let uu____73492 =
                                    FStar_TypeChecker_Tc.check_module tcenv
                                      fmod (FStar_Util.is_some pre_fn)
                                     in
                                  match uu____73492 with
                                  | (modul,env3) ->
                                      let smt_decls =
                                        let uu____73521 =
                                          let uu____73523 =
                                            FStar_Options.lax ()  in
                                          Prims.op_Negation uu____73523  in
                                        if uu____73521
                                        then
                                          let smt_decls =
                                            FStar_SMTEncoding_Encode.encode_modul
                                              env3 modul
                                             in
                                          (post_smt_encoding (); smt_decls)
                                        else ([], [])  in
                                      ((modul, smt_decls), env3))))
                        in
                     match uu____73434 with
                     | (((tcmod,smt_decls),env3),tc_time) ->
                         let uu____73610 =
                           with_env env3 (maybe_extract_mldefs tcmod)  in
                         (match uu____73610 with
                          | (extracted_defs,extract_time) ->
                              let uu____73641 =
                                with_env env3 (maybe_extract_ml_iface tcmod)
                                 in
                              (match uu____73641 with
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
                   let uu____73666 =
                     (FStar_Options.should_verify
                        (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                       &&
                       ((FStar_Options.record_hints ()) ||
                          (FStar_Options.use_hints ()))
                      in
                   if uu____73666
                   then
                     let uu____73677 = FStar_Parser_ParseIt.find_file fn  in
                     FStar_SMTEncoding_Solver.with_hints_db uu____73677
                       check_mod
                   else check_mod ()
                in
             let uu____73689 =
               let uu____73691 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____73691  in
             if uu____73689
             then
               let uu____73704 = load_module_from_cache env fn  in
               match uu____73704 with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____73718 =
                       let uu____73720 =
                         FStar_Parser_Dep.module_name_of_file fn  in
                       FStar_Options.should_be_already_cached uu____73720  in
                     if uu____73718
                     then
                       let uu____73723 =
                         let uu____73729 =
                           FStar_Util.format1
                             "Expected %s to already be checked" fn
                            in
                         (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                           uu____73729)
                          in
                       FStar_Errors.raise_err uu____73723
                     else ());
                    (let uu____73736 =
                       (let uu____73740 = FStar_Options.codegen ()  in
                        FStar_Option.isSome uu____73740) &&
                         (FStar_Options.cmi ())
                        in
                     if uu____73736
                     then
                       let uu____73744 =
                         let uu____73750 =
                           FStar_Util.format1
                             "Cross-module inlining expects all modules to be checked first; %s was not checked"
                             fn
                            in
                         (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                           uu____73750)
                          in
                       FStar_Errors.raise_err uu____73744
                     else ());
                    (let uu____73756 = tc_source_file ()  in
                     match uu____73756 with
                     | (tc_result,mllib,env1) ->
                         ((let uu____73783 =
                             (let uu____73787 = FStar_Errors.get_err_count ()
                                 in
                              uu____73787 = (Prims.parse_int "0")) &&
                               ((FStar_Options.lax ()) ||
                                  (FStar_Options.should_verify
                                     ((tc_result.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                              in
                           if uu____73783
                           then
                             store_module_to_cache env1 fn parsing_data
                               tc_result
                           else ());
                          (tc_result, mllib, env1,
                            FStar_Pervasives_Native.None))))
               | FStar_Pervasives_Native.Some tc_result ->
                   let tcmod = tc_result.checked_module  in
                   let smt_decls = tc_result.smt_decls  in
                   ((let uu____73809 =
                       FStar_Options.dump_module
                         (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                        in
                     if uu____73809
                     then
                       let uu____73812 =
                         FStar_Syntax_Print.modul_to_string tcmod  in
                       FStar_Util.print1 "Module after type checking:\n%s\n"
                         uu____73812
                     else ());
                    (let delta_tcenv tcmod1 tcenv =
                       let uu____73832 =
                         let uu____73837 =
                           FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                             tc_result.mii
                             (FStar_TypeChecker_Normalize.erase_universes
                                tcenv)
                            in
                         FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                           uu____73837
                          in
                       match uu____73832 with
                       | (uu____73853,tcenv1) ->
                           let env1 =
                             FStar_TypeChecker_Tc.load_checked_module tcenv1
                               tcmod1
                              in
                           ((let uu____73857 =
                               let uu____73859 = FStar_Options.lax ()  in
                               Prims.op_Negation uu____73859  in
                             if uu____73857
                             then
                               (FStar_SMTEncoding_Encode.encode_modul_from_cache
                                  env1 tcmod1.FStar_Syntax_Syntax.name
                                  smt_decls;
                                post_smt_encoding ())
                             else ());
                            ((), env1))
                        in
                     let mllib =
                       let uu____73868 =
                         ((let uu____73872 = FStar_Options.codegen ()  in
                           uu____73872 <> FStar_Pervasives_Native.None) &&
                            (FStar_Options.should_extract
                               (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                           &&
                           ((Prims.op_Negation
                               tcmod.FStar_Syntax_Syntax.is_interface)
                              ||
                              (let uu____73878 = FStar_Options.codegen ()  in
                               uu____73878 =
                                 (FStar_Pervasives_Native.Some
                                    FStar_Options.Kremlin)))
                          in
                       if uu____73868
                       then
                         with_env env
                           (fun env1  ->
                              let env2 = apply_delta_env env1 delta1  in
                              let extract_defs tcmod1 env3 =
                                let uu____73914 =
                                  with_tcenv_of_env env3 (delta_tcenv tcmod1)
                                   in
                                match uu____73914 with
                                | (uu____73926,env4) ->
                                    maybe_extract_mldefs tcmod1 env4
                                 in
                              let uu____73928 = extract_defs tcmod env2  in
                              match uu____73928 with
                              | (extracted_defs,extraction_time) ->
                                  extracted_defs)
                       else FStar_Pervasives_Native.None  in
                     let delta_env env1 =
                       FStar_Options.profile
                         (fun uu____73961  ->
                            let uu____73962 =
                              with_tcenv_of_env env1 (delta_tcenv tcmod)  in
                            match uu____73962 with
                            | (uu____73967,env2) ->
                                let uu____73969 =
                                  with_env env2
                                    (maybe_extract_ml_iface tcmod)
                                   in
                                (match uu____73969 with
                                 | (env3,_time) -> env3))
                         (fun uu____73985  ->
                            FStar_Util.format1
                              "Extending environment with module %s"
                              (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                        in
                     (tc_result, mllib, env,
                       (extend_delta_env delta1 delta_env))))
             else
               (let uu____73991 = tc_source_file ()  in
                match uu____73991 with
                | (tc_result,mllib,env1) ->
                    (tc_result, mllib, env1, FStar_Pervasives_Native.None)))
  
let (tc_one_file_for_ide :
  FStar_TypeChecker_Env.env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        FStar_Parser_Dep.parsing_data ->
          (tc_result * FStar_TypeChecker_Env.env_t))
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        fun parsing_data  ->
          let env1 = env_of_tcenv env  in
          let uu____74060 =
            tc_one_file env1 FStar_Pervasives_Native.None pre_fn fn
              parsing_data
             in
          match uu____74060 with
          | (tc_result,uu____74079,env2,delta1) ->
              let uu____74086 =
                let uu____74087 = apply_delta_env env2 delta1  in
                uu____74087.FStar_Extraction_ML_UEnv.env_tcenv  in
              (tc_result, uu____74086)
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____74110 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____74110 ["fsti"; "fsi"]))
        &&
        (let uu____74119 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____74119 ["fst"; "fs"])
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      delta_env ->
        FStar_Parser_Dep.deps ->
          (Prims.string Prims.list * tc_result Prims.list *
            FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option *
            uenv * delta_env))
  =
  fun remaining  ->
    fun env  ->
      fun delta_env  ->
        fun deps  ->
          let uu____74171 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____74220 =
                  let uu____74231 =
                    FStar_All.pipe_right impl
                      (FStar_Parser_Dep.parsing_data_of deps)
                     in
                  tc_one_file env delta_env
                    (FStar_Pervasives_Native.Some intf) impl uu____74231
                   in
                (match uu____74220 with
                 | (m,mllib,env1,delta_env1) ->
                     (remaining1, ([m], mllib, env1, delta_env1)))
            | intf_or_impl::remaining1 ->
                let uu____74287 =
                  let uu____74298 =
                    FStar_All.pipe_right intf_or_impl
                      (FStar_Parser_Dep.parsing_data_of deps)
                     in
                  tc_one_file env delta_env FStar_Pervasives_Native.None
                    intf_or_impl uu____74298
                   in
                (match uu____74287 with
                 | (m,mllib,env1,delta_env1) ->
                     (remaining1, ([m], mllib, env1, delta_env1)))
            | [] -> ([], ([], FStar_Pervasives_Native.None, env, delta_env))
             in
          match uu____74171 with
          | (remaining1,(nmods,mllib,env1,delta_env1)) ->
              (remaining1, nmods, mllib, env1, delta_env1)
  
let rec (tc_fold_interleave :
  FStar_Parser_Dep.deps ->
    (tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib Prims.list *
      uenv * delta_env) ->
      Prims.string Prims.list ->
        (tc_result Prims.list * FStar_Extraction_ML_Syntax.mllib Prims.list *
          uenv * delta_env))
  =
  fun deps  ->
    fun acc  ->
      fun remaining  ->
        let as_list uu___690_74490 =
          match uu___690_74490 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some l -> [l]  in
        match remaining with
        | [] -> acc
        | uu____74509 ->
            let uu____74513 = acc  in
            (match uu____74513 with
             | (mods,mllibs,env,delta_env) ->
                 let uu____74550 =
                   tc_one_file_from_remaining remaining env delta_env deps
                    in
                 (match uu____74550 with
                  | (remaining1,nmods,mllib,env1,delta_env1) ->
                      tc_fold_interleave deps
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
      (let uu____74634 = FStar_Options.debug_any ()  in
       if uu____74634
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____74642 =
             let uu____74644 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____74644  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____74642))
       else ());
      (let env =
         let uu____74660 = init_env dep_graph1  in
         FStar_Extraction_ML_UEnv.mkContext uu____74660  in
       let uu____74661 =
         tc_fold_interleave dep_graph1
           ([], [], env, FStar_Pervasives_Native.None) filenames
          in
       match uu____74661 with
       | (all_mods,mllibs,env1,delta1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____74713 =
                 with_tcenv_of_env env2
                   (fun tcenv  ->
                      (let uu____74722 =
                         (FStar_Options.interactive ()) &&
                           (let uu____74725 = FStar_Errors.get_err_count ()
                               in
                            uu____74725 = (Prims.parse_int "0"))
                          in
                       if uu____74722
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv))
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____74713
                in
             (all_mods, env1, (extend_delta_env delta1 solver_refresh)))))
  