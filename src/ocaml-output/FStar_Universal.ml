open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "5") 
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul ->
    (Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2)
  =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
  
type uenv = FStar_Extraction_ML_UEnv.uenv
type tc_result =
  {
  checked_module: FStar_Syntax_Syntax.modul ;
  checked_module_iface_opt:
    FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ;
  extracted_iface: FStar_Extraction_ML_Modul.iface ;
  mii: FStar_Syntax_DsEnv.module_inclusion_info ;
  tc_time: Prims.int ;
  extraction_time: Prims.int }
let (__proj__Mktc_result__item__checked_module :
  tc_result -> FStar_Syntax_Syntax.modul) =
  fun projectee  ->
    match projectee with
    | { checked_module; checked_module_iface_opt; extracted_iface; mii;
        tc_time; extraction_time;_} -> checked_module
  
let (__proj__Mktc_result__item__checked_module_iface_opt :
  tc_result -> FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { checked_module; checked_module_iface_opt; extracted_iface; mii;
        tc_time; extraction_time;_} -> checked_module_iface_opt
  
let (__proj__Mktc_result__item__extracted_iface :
  tc_result -> FStar_Extraction_ML_Modul.iface) =
  fun projectee  ->
    match projectee with
    | { checked_module; checked_module_iface_opt; extracted_iface; mii;
        tc_time; extraction_time;_} -> extracted_iface
  
let (__proj__Mktc_result__item__mii :
  tc_result -> FStar_Syntax_DsEnv.module_inclusion_info) =
  fun projectee  ->
    match projectee with
    | { checked_module; checked_module_iface_opt; extracted_iface; mii;
        tc_time; extraction_time;_} -> mii
  
let (__proj__Mktc_result__item__tc_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; checked_module_iface_opt; extracted_iface; mii;
        tc_time; extraction_time;_} -> tc_time
  
let (__proj__Mktc_result__item__extraction_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; checked_module_iface_opt; extracted_iface; mii;
        tc_time; extraction_time;_} -> extraction_time
  
let with_dsenv_of_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_Syntax_DsEnv.withenv ->
        ('a,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun tcenv  ->
    fun f  ->
      let uu____155 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____155 with
      | (a,dsenv1) ->
          (a,
            (let uu___456_169 = tcenv  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___456_169.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___456_169.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___456_169.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___456_169.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___456_169.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___456_169.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___456_169.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___456_169.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___456_169.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___456_169.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___456_169.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___456_169.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___456_169.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___456_169.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___456_169.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___456_169.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___456_169.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___456_169.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___456_169.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___456_169.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___456_169.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___456_169.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___456_169.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___456_169.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___456_169.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___456_169.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___456_169.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___456_169.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___456_169.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___456_169.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___456_169.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___456_169.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___456_169.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___456_169.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___456_169.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___456_169.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___456_169.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___456_169.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___456_169.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___456_169.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___456_169.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___456_169.FStar_TypeChecker_Env.nbe)
             }))
  
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env ->
         ('a,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2)
        -> ('a,uenv) FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun f  ->
      let uu____204 = f e.FStar_Extraction_ML_UEnv.env_tcenv  in
      match uu____204 with
      | (a,t') ->
          (a,
            (let uu___457_216 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___457_216.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___457_216.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___457_216.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___457_216.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let with_dsenv_of_env :
  'a .
    uenv ->
      'a FStar_Syntax_DsEnv.withenv ->
        ('a,uenv) FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun f  ->
      let uu____248 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f  in
      match uu____248 with
      | (a,tcenv) ->
          (a,
            (let uu___458_264 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___458_264.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___458_264.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___458_264.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___458_264.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____270 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____278 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env"
              in
           ((), uu____278))
       in
    FStar_Pervasives_Native.snd uu____270
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____284 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____292 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____292))
       in
    FStar_Pervasives_Native.snd uu____284
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____317 = pop_env env1  in res
  
let (env_of_tcenv :
  FStar_TypeChecker_Env.env -> FStar_Extraction_ML_UEnv.uenv) =
  fun env  -> FStar_Extraction_ML_UEnv.mkContext env 
let (parse :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        (FStar_Syntax_Syntax.modul,uenv) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____350 = FStar_Parser_Driver.parse_file fn  in
        match uu____350 with
        | (ast,uu____366) ->
            let uu____379 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____389 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____389 with
                   | (pre_ast,uu____405) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____424),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____435 =
                              let uu____440 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____440  in
                            (match uu____435 with
                             | (uu____453,env1) ->
                                 let uu____455 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____455)
                        | uu____464 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____379 with
             | (ast1,env1) ->
                 let uu____479 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____479)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____494 = FStar_Options.lax ()  in
      if uu____494
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___459_496 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___459_496.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___459_496.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___459_496.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___459_496.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___459_496.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_modul =
             (uu___459_496.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___459_496.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___459_496.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___459_496.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___459_496.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____498 =
        let uu____513 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____513  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____498
       in
    let env1 =
      let uu___460_517 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___460_517.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___460_517.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___460_517.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___460_517.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___460_517.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___460_517.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___460_517.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___460_517.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___460_517.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___460_517.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___460_517.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___460_517.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___460_517.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___460_517.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___460_517.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___460_517.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___460_517.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___460_517.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___460_517.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___460_517.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___460_517.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___460_517.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___460_517.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___460_517.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___460_517.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___460_517.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___460_517.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___460_517.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___460_517.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___460_517.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___460_517.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___460_517.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___460_517.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___460_517.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___460_517.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___460_517.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___460_517.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___460_517.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___460_517.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___460_517.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___460_517.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___460_517.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___461_519 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___461_519.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___461_519.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___461_519.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___461_519.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___461_519.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___461_519.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___461_519.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___461_519.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___461_519.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___461_519.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___461_519.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___461_519.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___461_519.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___461_519.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___461_519.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___461_519.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___461_519.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___461_519.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___461_519.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___461_519.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___461_519.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___461_519.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___461_519.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___461_519.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___461_519.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___461_519.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___461_519.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___461_519.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___461_519.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___461_519.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___461_519.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___461_519.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___461_519.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___461_519.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___461_519.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___461_519.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___461_519.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___461_519.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___461_519.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___461_519.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___461_519.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___461_519.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___462_521 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___462_521.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___462_521.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___462_521.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___462_521.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___462_521.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___462_521.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___462_521.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___462_521.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___462_521.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___462_521.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___462_521.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___462_521.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___462_521.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___462_521.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___462_521.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___462_521.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___462_521.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___462_521.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___462_521.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___462_521.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___462_521.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___462_521.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___462_521.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___462_521.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___462_521.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___462_521.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___462_521.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___462_521.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___462_521.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___462_521.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___462_521.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___462_521.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___462_521.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___462_521.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___462_521.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___462_521.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___462_521.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___462_521.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___462_521.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___462_521.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___462_521.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___462_521.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___463_523 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___463_523.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___463_523.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___463_523.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___463_523.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___463_523.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___463_523.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___463_523.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___463_523.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___463_523.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___463_523.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___463_523.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___463_523.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___463_523.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___463_523.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___463_523.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___463_523.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___463_523.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___463_523.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___463_523.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___463_523.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___463_523.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___463_523.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___463_523.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___463_523.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___463_523.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___463_523.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___463_523.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___463_523.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___463_523.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___463_523.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___463_523.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___463_523.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___463_523.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___463_523.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___463_523.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___463_523.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___463_523.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___463_523.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___463_523.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___463_523.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___463_523.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___463_523.FStar_TypeChecker_Env.nbe)
      }  in
    (env4.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env4; env4
  
let (tc_one_fragment :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env_t ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun curmod  ->
    fun env  ->
      fun frag  ->
        let acceptable_mod_name modul =
          let uu____556 =
            let uu____557 =
              let uu____558 = FStar_Options.file_list ()  in
              FStar_List.hd uu____558  in
            FStar_Parser_Dep.lowercase_module_name uu____557  in
          let uu____561 =
            let uu____562 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____562  in
          uu____556 = uu____561  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____569,{ FStar_Parser_AST.d = uu____570;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____572;
                           FStar_Parser_AST.quals = uu____573;
                           FStar_Parser_AST.attrs = uu____574;_}::uu____575)
              -> d
          | FStar_Parser_AST.Interface
              (uu____582,{ FStar_Parser_AST.d = uu____583;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____585;
                           FStar_Parser_AST.quals = uu____586;
                           FStar_Parser_AST.attrs = uu____587;_}::uu____588,uu____589)
              -> d
          | uu____596 -> FStar_Range.dummyRange  in
        let uu____597 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____597 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____609 =
              let uu____614 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____614  in
            (match uu____609 with
             | (ast_modul1,env1) ->
                 let uu____638 =
                   let uu____643 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____643
                    in
                 (match uu____638 with
                  | (modul,env2) ->
                      ((let uu____668 =
                          let uu____669 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____669  in
                        if uu____668
                        then
                          let msg =
                            let uu____671 =
                              let uu____672 =
                                let uu____673 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____673  in
                              FStar_Parser_Dep.module_name_of_file uu____672
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____671
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____677 =
                          let uu____688 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____688
                          then ((modul, []), env2)
                          else
                            (let uu____708 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____708 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____677 with
                        | ((modul1,uu____749),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____772 = FStar_List.hd ast_decls  in
                 (match uu____772 with
                  | { FStar_Parser_AST.d = uu____779;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____781;
                      FStar_Parser_AST.quals = uu____782;
                      FStar_Parser_AST.attrs = uu____783;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____793 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____811 =
                            let uu____818 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____818
                             in
                          match uu____811 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____793 with
                  | (env1,ast_decls_l) ->
                      let uu____872 =
                        let uu____877 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____877
                         in
                      (match uu____872 with
                       | (sigelts,env2) ->
                           let uu____901 =
                             let uu____910 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____910
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____901 with
                            | (modul1,uu____929,env3) ->
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
           (l,decls,uu____950)),uu____951)
          ->
          let uu____970 =
            let uu____975 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____975  in
          FStar_Pervasives_Native.snd uu____970
      | FStar_Parser_ParseIt.ASTFragment uu____991 ->
          let uu____1002 =
            let uu____1007 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____1007)  in
          FStar_Errors.raise_err uu____1002
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____1011 ->
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
    let uu____1100 = FStar_Util.load_value_from_file cache_file  in
    match uu____1100 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inl "Corrupt"
    | FStar_Pervasives_Native.Some (vnum,digest,tc_result) ->
        if vnum <> cache_version_number
        then FStar_Util.Inl "Stale, because inconsistent cache version"
        else
          (let uu____1175 =
             let uu____1184 = FStar_TypeChecker_Env.dep_graph env  in
             FStar_Parser_Dep.hash_dependences uu____1184 source_file  in
           match uu____1175 with
           | FStar_Pervasives_Native.Some digest' ->
               if digest = digest'
               then FStar_Util.Inr tc_result
               else
                 ((let uu____1214 = FStar_Options.debug_any ()  in
                   if uu____1214
                   then
                     ((let uu____1216 =
                         FStar_Util.string_of_int (FStar_List.length digest')
                          in
                       let uu____1221 = FStar_Parser_Dep.print_digest digest'
                          in
                       let uu____1222 =
                         FStar_Util.string_of_int (FStar_List.length digest)
                          in
                       let uu____1227 = FStar_Parser_Dep.print_digest digest
                          in
                       FStar_Util.print4
                         "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                         uu____1216 uu____1221 uu____1222 uu____1227);
                      if
                        (FStar_List.length digest) =
                          (FStar_List.length digest')
                      then
                        FStar_List.iter2
                          (fun uu____1252  ->
                             fun uu____1253  ->
                               match (uu____1252, uu____1253) with
                               | ((x,y),(x',y')) ->
                                   if (x <> x') || (y <> y')
                                   then
                                     let uu____1282 =
                                       FStar_Parser_Dep.print_digest [(x, y)]
                                        in
                                     let uu____1291 =
                                       FStar_Parser_Dep.print_digest
                                         [(x', y')]
                                        in
                                     FStar_Util.print2
                                       "Differ at: Expected %s\n Got %s\n"
                                       uu____1282 uu____1291
                                   else ()) digest digest'
                      else ())
                   else ());
                  FStar_Util.Inl "Stale")
           | uu____1303 -> FStar_Util.Inl "Unable to compute digest of")
     in
  fun env  ->
    fun fn  ->
      let cache_file = FStar_Parser_Dep.cache_file_name fn  in
      let fail1 tag should_warn cache_file1 =
        invalidate_cache ();
        if should_warn
        then
          (let uu____1335 =
             let uu____1336 =
               FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
                in
             let uu____1337 =
               FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
                in
             FStar_Range.mk_range fn uu____1336 uu____1337  in
           let uu____1338 =
             let uu____1343 =
               FStar_Util.format3
                 "%s cache file %s; will recheck %s and all subsequent files"
                 tag cache_file1 fn
                in
             (FStar_Errors.Warning_CachedFile, uu____1343)  in
           FStar_Errors.log_issue uu____1335 uu____1338)
        else ();
        FStar_Pervasives_Native.None  in
      let uu____1345 = FStar_ST.op_Bang some_cache_invalid  in
      match uu____1345 with
      | FStar_Pervasives_Native.Some uu____1395 ->
          FStar_Pervasives_Native.None
      | uu____1396 ->
          if FStar_Util.file_exists cache_file
          then
            let uu____1401 =
              load1 env.FStar_Extraction_ML_UEnv.env_tcenv fn cache_file  in
            (match uu____1401 with
             | FStar_Util.Inl msg -> fail1 msg true cache_file
             | FStar_Util.Inr res -> FStar_Pervasives_Native.Some res)
          else
            (let uu____1411 =
               let uu____1414 = FStar_Util.basename cache_file  in
               FStar_Options.find_file uu____1414  in
             match uu____1411 with
             | FStar_Pervasives_Native.None  ->
                 fail1 "Absent" false cache_file
             | FStar_Pervasives_Native.Some alt_cache_file ->
                 let uu____1418 =
                   load1 env.FStar_Extraction_ML_UEnv.env_tcenv fn
                     alt_cache_file
                    in
                 (match uu____1418 with
                  | FStar_Util.Inl msg -> fail1 msg true alt_cache_file
                  | FStar_Util.Inr res ->
                      ((let uu____1428 = FStar_Options.should_verify_file fn
                           in
                        if uu____1428
                        then FStar_Util.copy_file alt_cache_file cache_file
                        else ());
                       FStar_Pervasives_Native.Some res)))
  
let (store_module_to_cache : uenv -> Prims.string -> tc_result -> unit) =
  fun env  ->
    fun fn  ->
      fun tc_result  ->
        let uu____1445 =
          (FStar_Options.cache_checked_modules ()) &&
            (let uu____1447 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____1447)
           in
        if uu____1445
        then
          let cache_file = FStar_Parser_Dep.cache_file_name fn  in
          let digest =
            let uu____1458 =
              FStar_TypeChecker_Env.dep_graph
                env.FStar_Extraction_ML_UEnv.env_tcenv
               in
            FStar_Parser_Dep.hash_dependences uu____1458 fn  in
          match digest with
          | FStar_Pervasives_Native.Some hashes ->
              let tc_result1 =
                let uu___464_1473 = tc_result  in
                {
                  checked_module = (uu___464_1473.checked_module);
                  checked_module_iface_opt =
                    (uu___464_1473.checked_module_iface_opt);
                  extracted_iface = (uu___464_1473.extracted_iface);
                  mii = (uu___464_1473.mii);
                  tc_time = (Prims.parse_int "0");
                  extraction_time = (Prims.parse_int "0")
                }  in
              FStar_Util.save_value_to_file cache_file
                (cache_version_number, hashes, tc_result1)
          | uu____1492 ->
              let uu____1501 =
                let uu____1502 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                let uu____1503 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range fn uu____1502 uu____1503  in
              let uu____1504 =
                let uu____1509 =
                  FStar_Util.format1
                    "%s was not written, since some of its dependences were not also checked"
                    cache_file
                   in
                (FStar_Errors.Warning_FileNotWritten, uu____1509)  in
              FStar_Errors.log_issue uu____1501 uu____1504
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
            ((fun e  -> let uu____1587 = f1 e  in g uu____1587))
  
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
        | uu____1603 -> failwith "Unrecognized option"  in
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
            let uu____1622 =
              FStar_List.map FStar_Extraction_Kremlin.translate mllibs  in
            FStar_List.flatten uu____1622  in
          let bin = (FStar_Extraction_Kremlin.current_version, programs)  in
          (match programs with
           | (name,uu____1645)::[] ->
               let uu____1654 =
                 FStar_Options.prepend_output_dir (Prims.strcat name ext)  in
               FStar_Util.save_value_to_file uu____1654 bin
           | uu____1655 ->
               let uu____1662 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____1662 bin)
      | uu____1663 -> failwith "Unrecognized option"
    else ()
  
let (tc_one_file :
  uenv ->
    delta_env ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          (tc_result,uenv,delta_env) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun delta1  ->
      fun pre_fn  ->
        fun fn  ->
          FStar_Syntax_Syntax.reset_gensym ();
          (let maybe_extract_mldefs tcmod env1 =
             let uu____1725 =
               (let uu____1728 = FStar_Options.codegen ()  in
                uu____1728 = FStar_Pervasives_Native.None) ||
                 (let uu____1734 =
                    FStar_Options.should_extract
                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  Prims.op_Negation uu____1734)
                in
             if uu____1725
             then (FStar_Pervasives_Native.None, (Prims.parse_int "0"))
             else
               FStar_Util.record_time
                 (fun uu____1759  ->
                    let uu____1760 =
                      FStar_Extraction_ML_Modul.extract env1 tcmod  in
                    match uu____1760 with
                    | (uu____1771,defs) ->
                        (emit defs; FStar_Pervasives_Native.Some defs))
              in
           let tc_source_file uu____1789 =
             let env1 = apply_delta_env env delta1  in
             let uu____1793 = parse env1 pre_fn fn  in
             match uu____1793 with
             | (fmod,env2) ->
                 let mii =
                   FStar_Syntax_DsEnv.inclusion_info
                     (env2.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                     fmod.FStar_Syntax_Syntax.name
                    in
                 let check_mod uu____1814 =
                   let uu____1815 =
                     FStar_Util.record_time
                       (fun uu____1841  ->
                          with_tcenv_of_env env2
                            (fun tcenv  ->
                               FStar_TypeChecker_Tc.check_module tcenv fmod
                                 (FStar_Util.is_some pre_fn)))
                      in
                   match uu____1815 with
                   | (((tcmod,tcmod_iface_opt),env3),tc_time) ->
                       let uu____1878 =
                         with_env env3 (maybe_extract_mldefs tcmod)  in
                       (match uu____1878 with
                        | (extracted_defs,extract_time) ->
                            let uu____1909 =
                              FStar_Util.record_time
                                (fun uu____1923  ->
                                   FStar_Extraction_ML_Modul.extract_iface
                                     env3 tcmod)
                               in
                            (match uu____1909 with
                             | ((env4,extracted_iface),iface_extract_time) ->
                                 ({
                                    checked_module = tcmod;
                                    checked_module_iface_opt =
                                      tcmod_iface_opt;
                                    extracted_iface;
                                    mii;
                                    tc_time;
                                    extraction_time =
                                      (iface_extract_time + extract_time)
                                  }, env4)))
                    in
                 let uu____1935 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                    in
                 if uu____1935
                 then
                   let uu____1940 = FStar_Parser_ParseIt.find_file fn  in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1940
                     check_mod
                 else check_mod ()
              in
           let uu____1946 =
             let uu____1947 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____1947  in
           if uu____1946
           then
             let uu____1954 = load_module_from_cache env fn  in
             match uu____1954 with
             | FStar_Pervasives_Native.None  ->
                 let uu____1963 = tc_source_file ()  in
                 (match uu____1963 with
                  | (tc_result,env1) ->
                      ((let uu____1977 =
                          (let uu____1980 = FStar_Errors.get_err_count ()  in
                           uu____1980 = (Prims.parse_int "0")) &&
                            ((FStar_Options.lax ()) ||
                               (FStar_Options.should_verify
                                  ((tc_result.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                           in
                        if uu____1977
                        then store_module_to_cache env1 fn tc_result
                        else ());
                       (tc_result, env1, FStar_Pervasives_Native.None)))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.checked_module  in
                 ((let uu____1988 =
                     FStar_Options.dump_module
                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____1988
                   then
                     let uu____1989 =
                       FStar_Syntax_Print.modul_to_string tcmod  in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____1989
                   else ());
                  (let delta_tcenv tcmod1 tcenv =
                     let uu____2006 =
                       let uu____2011 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                           tc_result.mii
                           (FStar_TypeChecker_Normalize.erase_universes tcenv)
                          in
                       FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                         uu____2011
                        in
                     match uu____2006 with
                     | (uu____2031,tcenv1) ->
                         let uu____2033 =
                           FStar_TypeChecker_Tc.load_checked_module tcenv1
                             tcmod1
                            in
                         ((), uu____2033)
                      in
                   (let uu____2035 =
                      ((let uu____2038 = FStar_Options.codegen ()  in
                        uu____2038 <> FStar_Pervasives_Native.None) &&
                         (FStar_Options.should_extract
                            (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                        &&
                        (Prims.op_Negation
                           tcmod.FStar_Syntax_Syntax.is_interface)
                       in
                    if uu____2035
                    then
                      with_env env
                        (fun env1  ->
                           let env2 = apply_delta_env env1 delta1  in
                           let extract_defs tcmod1 env3 =
                             let uu____2072 =
                               with_tcenv_of_env env3 (delta_tcenv tcmod1)
                                in
                             match uu____2072 with
                             | (uu____2085,env4) ->
                                 maybe_extract_mldefs tcmod1 env4
                              in
                           let uu____2087 = extract_defs tcmod env2  in ())
                    else ());
                   (let delta_env env1 =
                      let tcmod_or_iface =
                        if tcmod.FStar_Syntax_Syntax.is_interface
                        then tcmod
                        else
                          (let use_interface_from_the_cache =
                             ((FStar_Options.use_extracted_interfaces ()) &&
                                (pre_fn = FStar_Pervasives_Native.None))
                               &&
                               (let uu____2109 =
                                  (FStar_Options.expose_interfaces ()) &&
                                    (FStar_Options.should_verify
                                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                                   in
                                Prims.op_Negation uu____2109)
                              in
                           if use_interface_from_the_cache
                           then
                             (if
                                FStar_Option.isNone
                                  tc_result.checked_module_iface_opt
                              then
                                ((let uu____2111 =
                                    let uu____2112 =
                                      FStar_Range.mk_pos
                                        (Prims.parse_int "0")
                                        (Prims.parse_int "0")
                                       in
                                    let uu____2113 =
                                      FStar_Range.mk_pos
                                        (Prims.parse_int "0")
                                        (Prims.parse_int "0")
                                       in
                                    FStar_Range.mk_range
                                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                                      uu____2112 uu____2113
                                     in
                                  FStar_Errors.log_issue uu____2111
                                    (FStar_Errors.Warning_MissingInterfaceOrImplementation,
                                      (Prims.strcat
                                         "use_extracted_interfaces option is set but could not find an interface in the cache for: "
                                         (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)));
                                 tcmod)
                              else
                                FStar_Option.get
                                  tc_result.checked_module_iface_opt)
                           else tcmod)
                         in
                      let uu____2116 =
                        with_tcenv_of_env env1 (delta_tcenv tcmod_or_iface)
                         in
                      match uu____2116 with
                      | (uu____2121,env2) ->
                          FStar_Extraction_ML_Modul.extend_with_iface env2
                            tc_result.extracted_iface
                       in
                    (tc_result, env, (extend_delta_env delta1 delta_env)))))
           else
             (let uu____2127 = tc_source_file ()  in
              match uu____2127 with
              | (tc_result,env1) ->
                  (tc_result, env1, FStar_Pervasives_Native.None)))
  
let (tc_one_file_for_ide :
  FStar_TypeChecker_Env.env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        (tc_result,FStar_TypeChecker_Env.env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let env1 = env_of_tcenv env  in
        let uu____2171 =
          tc_one_file env1 FStar_Pervasives_Native.None pre_fn fn  in
        match uu____2171 with
        | (tc_result,env2,delta1) ->
            let uu____2188 =
              let uu____2189 = apply_delta_env env2 delta1  in
              uu____2189.FStar_Extraction_ML_UEnv.env_tcenv  in
            (tc_result, uu____2188)
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____2205 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____2205 ["fsti"; "fsi"]))
        &&
        (let uu____2207 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____2207 ["fst"; "fs"])
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      delta_env ->
        (Prims.string Prims.list,tc_result Prims.list,uenv,delta_env)
          FStar_Pervasives_Native.tuple4)
  =
  fun remaining  ->
    fun env  ->
      fun delta_env  ->
        let uu____2241 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____2275 =
                tc_one_file env delta_env (FStar_Pervasives_Native.Some intf)
                  impl
                 in
              (match uu____2275 with
               | (m,env1,delta_env1) -> (remaining1, ([m], env1, delta_env1)))
          | intf_or_impl::remaining1 ->
              let uu____2319 =
                tc_one_file env delta_env FStar_Pervasives_Native.None
                  intf_or_impl
                 in
              (match uu____2319 with
               | (m,env1,delta_env1) -> (remaining1, ([m], env1, delta_env1)))
          | [] -> ([], ([], env, delta_env))  in
        match uu____2241 with
        | (remaining1,(nmods,env1,delta_env1)) ->
            (remaining1, nmods, env1, delta_env1)
  
let rec (tc_fold_interleave :
  (tc_result Prims.list,uenv,delta_env) FStar_Pervasives_Native.tuple3 ->
    Prims.string Prims.list ->
      (tc_result Prims.list,uenv,delta_env) FStar_Pervasives_Native.tuple3)
  =
  fun acc  ->
    fun remaining  ->
      match remaining with
      | [] -> acc
      | uu____2457 ->
          let uu____2460 = acc  in
          (match uu____2460 with
           | (mods,env,delta_env) ->
               let uu____2484 =
                 tc_one_file_from_remaining remaining env delta_env  in
               (match uu____2484 with
                | (remaining1,nmods,env1,delta_env1) ->
                    tc_fold_interleave
                      ((FStar_List.append mods nmods), env1, delta_env1)
                      remaining1))
  
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      (tc_result Prims.list,uenv,(uenv -> uenv)
                                   FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun filenames  ->
    fun dep_graph1  ->
      (let uu____2551 = FStar_Options.debug_any ()  in
       if uu____2551
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____2554 =
             let uu____2555 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____2555  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____2554))
       else ());
      (let env =
         let uu____2564 = init_env dep_graph1  in
         FStar_Extraction_ML_UEnv.mkContext uu____2564  in
       let uu____2565 =
         tc_fold_interleave ([], env, FStar_Pervasives_Native.None) filenames
          in
       match uu____2565 with
       | (all_mods,env1,delta1) ->
           let solver_refresh env2 =
             let uu____2605 =
               with_tcenv_of_env env2
                 (fun tcenv  ->
                    (let uu____2614 =
                       (FStar_Options.interactive ()) &&
                         (let uu____2616 = FStar_Errors.get_err_count ()  in
                          uu____2616 = (Prims.parse_int "0"))
                        in
                     if uu____2614
                     then
                       (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                         ()
                     else
                       (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                         ());
                    ((), tcenv))
                in
             FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2605  in
           (all_mods, env1, (extend_delta_env delta1 solver_refresh)))
  