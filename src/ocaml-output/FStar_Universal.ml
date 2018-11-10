open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "6") 
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
  extracted_iface: FStar_Extraction_ML_Modul.iface ;
  mii: FStar_Syntax_DsEnv.module_inclusion_info ;
  tc_time: Prims.int ;
  extraction_time: Prims.int }
let (__proj__Mktc_result__item__checked_module :
  tc_result -> FStar_Syntax_Syntax.modul) =
  fun projectee  ->
    match projectee with
    | { checked_module; extracted_iface; mii; tc_time; extraction_time;_} ->
        checked_module
  
let (__proj__Mktc_result__item__extracted_iface :
  tc_result -> FStar_Extraction_ML_Modul.iface) =
  fun projectee  ->
    match projectee with
    | { checked_module; extracted_iface; mii; tc_time; extraction_time;_} ->
        extracted_iface
  
let (__proj__Mktc_result__item__mii :
  tc_result -> FStar_Syntax_DsEnv.module_inclusion_info) =
  fun projectee  ->
    match projectee with
    | { checked_module; extracted_iface; mii; tc_time; extraction_time;_} ->
        mii
  
let (__proj__Mktc_result__item__tc_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; extracted_iface; mii; tc_time; extraction_time;_} ->
        tc_time
  
let (__proj__Mktc_result__item__extraction_time : tc_result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { checked_module; extracted_iface; mii; tc_time; extraction_time;_} ->
        extraction_time
  
let with_dsenv_of_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_Syntax_DsEnv.withenv ->
        ('a,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun tcenv  ->
    fun f  ->
      let uu____143 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____143 with
      | (a,dsenv1) ->
          (a,
            (let uu___456_157 = tcenv  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___456_157.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___456_157.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___456_157.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___456_157.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___456_157.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___456_157.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___456_157.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___456_157.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___456_157.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___456_157.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___456_157.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___456_157.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___456_157.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___456_157.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___456_157.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___456_157.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___456_157.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___456_157.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___456_157.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___456_157.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___456_157.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___456_157.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___456_157.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___456_157.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___456_157.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___456_157.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___456_157.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___456_157.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___456_157.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___456_157.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___456_157.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___456_157.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___456_157.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___456_157.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___456_157.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___456_157.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___456_157.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___456_157.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___456_157.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___456_157.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___456_157.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___456_157.FStar_TypeChecker_Env.nbe)
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
      let uu____193 = f e.FStar_Extraction_ML_UEnv.env_tcenv  in
      match uu____193 with
      | (a,t') ->
          (a,
            (let uu___457_205 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___457_205.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___457_205.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___457_205.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___457_205.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let with_dsenv_of_env :
  'a .
    uenv ->
      'a FStar_Syntax_DsEnv.withenv ->
        ('a,uenv) FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun f  ->
      let uu____238 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f  in
      match uu____238 with
      | (a,tcenv) ->
          (a,
            (let uu___458_254 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___458_254.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___458_254.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___458_254.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___458_254.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____261 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____269 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env"
              in
           ((), uu____269))
       in
    FStar_Pervasives_Native.snd uu____261
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____277 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____285 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____285))
       in
    FStar_Pervasives_Native.snd uu____277
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____312 = pop_env env1  in res
  
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
        let uu____351 = FStar_Parser_Driver.parse_file fn  in
        match uu____351 with
        | (ast,uu____368) ->
            let uu____383 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____396 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____396 with
                   | (pre_ast,uu____413) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____434),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____447 =
                              let uu____452 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____452  in
                            (match uu____447 with
                             | (uu____465,env1) ->
                                 let uu____467 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____467)
                        | uu____477 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____383 with
             | (ast1,env1) ->
                 let uu____494 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____494)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____510 = FStar_Options.lax ()  in
      if uu____510
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___459_515 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___459_515.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___459_515.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___459_515.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___459_515.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___459_515.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_modul =
             (uu___459_515.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___459_515.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___459_515.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___459_515.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___459_515.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____517 =
        let uu____532 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____532  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____517
       in
    let env1 =
      let uu___460_536 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___460_536.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___460_536.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___460_536.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___460_536.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___460_536.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___460_536.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___460_536.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___460_536.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___460_536.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___460_536.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___460_536.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___460_536.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___460_536.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___460_536.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___460_536.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___460_536.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___460_536.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___460_536.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___460_536.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___460_536.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___460_536.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___460_536.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___460_536.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___460_536.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___460_536.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___460_536.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___460_536.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___460_536.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___460_536.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___460_536.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___460_536.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___460_536.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___460_536.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___460_536.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___460_536.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___460_536.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___460_536.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___460_536.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___460_536.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___460_536.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___460_536.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___460_536.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___461_538 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___461_538.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___461_538.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___461_538.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___461_538.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___461_538.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___461_538.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___461_538.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___461_538.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___461_538.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___461_538.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___461_538.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___461_538.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___461_538.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___461_538.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___461_538.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___461_538.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___461_538.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___461_538.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___461_538.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___461_538.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___461_538.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___461_538.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___461_538.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___461_538.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___461_538.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___461_538.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___461_538.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___461_538.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___461_538.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___461_538.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___461_538.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___461_538.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___461_538.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___461_538.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___461_538.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___461_538.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___461_538.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___461_538.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___461_538.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___461_538.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___461_538.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___461_538.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___462_540 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___462_540.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___462_540.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___462_540.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___462_540.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___462_540.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___462_540.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___462_540.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___462_540.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___462_540.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___462_540.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___462_540.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___462_540.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___462_540.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___462_540.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___462_540.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___462_540.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___462_540.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___462_540.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___462_540.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___462_540.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___462_540.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___462_540.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___462_540.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___462_540.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___462_540.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___462_540.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___462_540.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___462_540.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___462_540.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___462_540.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___462_540.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___462_540.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___462_540.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___462_540.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___462_540.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___462_540.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___462_540.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___462_540.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___462_540.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___462_540.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___462_540.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___462_540.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___463_542 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___463_542.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___463_542.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___463_542.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___463_542.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___463_542.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___463_542.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___463_542.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___463_542.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___463_542.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___463_542.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___463_542.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___463_542.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___463_542.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___463_542.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___463_542.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___463_542.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___463_542.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___463_542.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___463_542.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___463_542.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___463_542.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___463_542.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___463_542.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___463_542.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___463_542.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___463_542.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___463_542.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___463_542.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___463_542.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___463_542.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___463_542.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___463_542.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___463_542.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___463_542.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___463_542.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___463_542.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___463_542.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___463_542.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___463_542.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___463_542.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___463_542.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___463_542.FStar_TypeChecker_Env.nbe)
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
          let uu____577 =
            let uu____579 =
              let uu____581 = FStar_Options.file_list ()  in
              FStar_List.hd uu____581  in
            FStar_Parser_Dep.lowercase_module_name uu____579  in
          let uu____586 =
            let uu____588 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____588  in
          uu____577 = uu____586  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____597,{ FStar_Parser_AST.d = uu____598;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____600;
                           FStar_Parser_AST.quals = uu____601;
                           FStar_Parser_AST.attrs = uu____602;_}::uu____603)
              -> d
          | FStar_Parser_AST.Interface
              (uu____610,{ FStar_Parser_AST.d = uu____611;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____613;
                           FStar_Parser_AST.quals = uu____614;
                           FStar_Parser_AST.attrs = uu____615;_}::uu____616,uu____617)
              -> d
          | uu____626 -> FStar_Range.dummyRange  in
        let uu____627 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____627 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____639 =
              let uu____644 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____644  in
            (match uu____639 with
             | (ast_modul1,env1) ->
                 let uu____669 =
                   let uu____674 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____674
                    in
                 (match uu____669 with
                  | (modul,env2) ->
                      ((let uu____699 =
                          let uu____701 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____701  in
                        if uu____699
                        then
                          let msg =
                            let uu____706 =
                              let uu____708 =
                                let uu____710 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____710  in
                              FStar_Parser_Dep.module_name_of_file uu____708
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____706
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____719 =
                          let uu____730 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____730
                          then ((modul, []), env2)
                          else
                            (let uu____753 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____753 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____719 with
                        | ((modul1,uu____794),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____817 = FStar_List.hd ast_decls  in
                 (match uu____817 with
                  | { FStar_Parser_AST.d = uu____824;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____826;
                      FStar_Parser_AST.quals = uu____827;
                      FStar_Parser_AST.attrs = uu____828;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____840 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____858 =
                            let uu____865 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____865
                             in
                          match uu____858 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____840 with
                  | (env1,ast_decls_l) ->
                      let uu____919 =
                        let uu____924 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____924
                         in
                      (match uu____919 with
                       | (sigelts,env2) ->
                           let uu____948 =
                             let uu____957 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____957
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____948 with
                            | (modul1,uu____979,env3) ->
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
           (l,decls,uu____1003)),uu____1004)
          ->
          let uu____1027 =
            let uu____1032 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____1032  in
          FStar_Pervasives_Native.snd uu____1027
      | FStar_Parser_ParseIt.ASTFragment uu____1048 ->
          let uu____1060 =
            let uu____1066 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____1066)  in
          FStar_Errors.raise_err uu____1060
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____1076 ->
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
    let uu____1173 = FStar_Util.load_value_from_file cache_file  in
    match uu____1173 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inl "Corrupt"
    | FStar_Pervasives_Native.Some (vnum,digest,tc_result) ->
        if vnum <> cache_version_number
        then FStar_Util.Inl "Stale, because inconsistent cache version"
        else
          (let uu____1275 =
             let uu____1286 = FStar_TypeChecker_Env.dep_graph env  in
             FStar_Parser_Dep.hash_dependences uu____1286 source_file  in
           match uu____1275 with
           | FStar_Pervasives_Native.Some digest' ->
               if digest = digest'
               then FStar_Util.Inr tc_result
               else
                 ((let uu____1327 = FStar_Options.debug_any ()  in
                   if uu____1327
                   then
                     ((let uu____1331 =
                         FStar_Util.string_of_int (FStar_List.length digest')
                          in
                       let uu____1339 = FStar_Parser_Dep.print_digest digest'
                          in
                       let uu____1341 =
                         FStar_Util.string_of_int (FStar_List.length digest)
                          in
                       let uu____1349 = FStar_Parser_Dep.print_digest digest
                          in
                       FStar_Util.print4
                         "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                         uu____1331 uu____1339 uu____1341 uu____1349);
                      if
                        (FStar_List.length digest) =
                          (FStar_List.length digest')
                      then
                        FStar_List.iter2
                          (fun uu____1385  ->
                             fun uu____1386  ->
                               match (uu____1385, uu____1386) with
                               | ((x,y),(x',y')) ->
                                   if (x <> x') || (y <> y')
                                   then
                                     let uu____1438 =
                                       FStar_Parser_Dep.print_digest [(x, y)]
                                        in
                                     let uu____1454 =
                                       FStar_Parser_Dep.print_digest
                                         [(x', y')]
                                        in
                                     FStar_Util.print2
                                       "Differ at: Expected %s\n Got %s\n"
                                       uu____1438 uu____1454
                                   else ()) digest digest'
                      else ())
                   else ());
                  FStar_Util.Inl "Stale")
           | uu____1479 -> FStar_Util.Inl "Unable to compute digest of")
     in
  fun env  ->
    fun fn  ->
      let cache_file = FStar_Parser_Dep.cache_file_name fn  in
      let fail1 tag should_warn cache_file1 =
        invalidate_cache ();
        if should_warn
        then
          (let uu____1524 =
             let uu____1525 =
               FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
                in
             let uu____1528 =
               FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
                in
             FStar_Range.mk_range fn uu____1525 uu____1528  in
           let uu____1531 =
             let uu____1537 =
               FStar_Util.format3
                 "%s cache file %s; will recheck %s and all subsequent files"
                 tag cache_file1 fn
                in
             (FStar_Errors.Warning_CachedFile, uu____1537)  in
           FStar_Errors.log_issue uu____1524 uu____1531)
        else ();
        FStar_Pervasives_Native.None  in
      let uu____1543 = FStar_ST.op_Bang some_cache_invalid  in
      match uu____1543 with
      | FStar_Pervasives_Native.Some uu____1593 ->
          FStar_Pervasives_Native.None
      | uu____1594 ->
          if FStar_Util.file_exists cache_file
          then
            let uu____1600 =
              load1 env.FStar_Extraction_ML_UEnv.env_tcenv fn cache_file  in
            (match uu____1600 with
             | FStar_Util.Inl msg -> fail1 msg true cache_file
             | FStar_Util.Inr res -> FStar_Pervasives_Native.Some res)
          else
            (let uu____1616 =
               let uu____1620 = FStar_Util.basename cache_file  in
               FStar_Options.find_file uu____1620  in
             match uu____1616 with
             | FStar_Pervasives_Native.None  ->
                 fail1 "Absent" false cache_file
             | FStar_Pervasives_Native.Some alt_cache_file ->
                 let uu____1630 =
                   load1 env.FStar_Extraction_ML_UEnv.env_tcenv fn
                     alt_cache_file
                    in
                 (match uu____1630 with
                  | FStar_Util.Inl msg -> fail1 msg true alt_cache_file
                  | FStar_Util.Inr res ->
                      ((let uu____1645 = FStar_Options.should_verify_file fn
                           in
                        if uu____1645
                        then FStar_Util.copy_file alt_cache_file cache_file
                        else ());
                       FStar_Pervasives_Native.Some res)))
  
let (store_module_to_cache : uenv -> Prims.string -> tc_result -> unit) =
  fun env  ->
    fun fn  ->
      fun tc_result  ->
        let uu____1668 =
          (FStar_Options.cache_checked_modules ()) &&
            (let uu____1671 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____1671)
           in
        if uu____1668
        then
          let cache_file = FStar_Parser_Dep.cache_file_name fn  in
          let digest =
            let uu____1687 =
              FStar_TypeChecker_Env.dep_graph
                env.FStar_Extraction_ML_UEnv.env_tcenv
               in
            FStar_Parser_Dep.hash_dependences uu____1687 fn  in
          match digest with
          | FStar_Pervasives_Native.Some hashes ->
              let tc_result1 =
                let uu___464_1706 = tc_result  in
                {
                  checked_module = (uu___464_1706.checked_module);
                  extracted_iface = (uu___464_1706.extracted_iface);
                  mii = (uu___464_1706.mii);
                  tc_time = (Prims.parse_int "0");
                  extraction_time = (Prims.parse_int "0")
                }  in
              FStar_Util.save_value_to_file cache_file
                (cache_version_number, hashes, tc_result1)
          | uu____1733 ->
              let uu____1744 =
                let uu____1745 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                let uu____1748 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range fn uu____1745 uu____1748  in
              let uu____1751 =
                let uu____1757 =
                  FStar_Util.format1
                    "%s was not written, since some of its dependences were not also checked"
                    cache_file
                   in
                (FStar_Errors.Warning_FileNotWritten, uu____1757)  in
              FStar_Errors.log_issue uu____1744 uu____1751
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
            ((fun e  -> let uu____1841 = f1 e  in g uu____1841))
  
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
        | uu____1865 -> failwith "Unrecognized option"  in
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
           | (name,uu____1890)::[] ->
               let uu____1893 =
                 FStar_Options.prepend_output_dir (Prims.strcat name ext)  in
               FStar_Util.save_value_to_file uu____1893 bin
           | uu____1895 ->
               let uu____1898 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____1898 bin)
      | uu____1901 -> failwith "Unrecognized option"
    else ()
  
let (tc_one_file :
  uenv ->
    delta_env ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          (tc_result,FStar_Extraction_ML_Syntax.mllib
                       FStar_Pervasives_Native.option,uenv,delta_env)
            FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun delta1  ->
      fun pre_fn  ->
        fun fn  ->
          FStar_Syntax_Syntax.reset_gensym ();
          (let maybe_extract_mldefs tcmod env1 =
             let uu____1977 =
               (let uu____1981 = FStar_Options.codegen ()  in
                uu____1981 = FStar_Pervasives_Native.None) ||
                 (let uu____1987 =
                    FStar_Options.should_extract
                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                     in
                  Prims.op_Negation uu____1987)
                in
             if uu____1977
             then (FStar_Pervasives_Native.None, (Prims.parse_int "0"))
             else
               FStar_Util.record_time
                 (fun uu____2009  ->
                    let uu____2010 =
                      FStar_Extraction_ML_Modul.extract env1 tcmod  in
                    match uu____2010 with | (uu____2019,defs) -> defs)
              in
           let tc_source_file uu____2038 =
             let env1 = apply_delta_env env delta1  in
             let uu____2042 = parse env1 pre_fn fn  in
             match uu____2042 with
             | (fmod,env2) ->
                 let mii =
                   FStar_Syntax_DsEnv.inclusion_info
                     (env2.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                     fmod.FStar_Syntax_Syntax.name
                    in
                 let check_mod uu____2071 =
                   let uu____2072 =
                     FStar_Util.record_time
                       (fun uu____2087  ->
                          with_tcenv_of_env env2
                            (fun tcenv  ->
                               (match tcenv.FStar_TypeChecker_Env.gamma with
                                | [] -> ()
                                | uu____2092 ->
                                    failwith
                                      "Impossible: gamma contains leaked names");
                               FStar_TypeChecker_Tc.check_module tcenv fmod
                                 (FStar_Util.is_some pre_fn)))
                      in
                   match uu____2072 with
                   | ((tcmod,env3),tc_time) ->
                       let uu____2114 =
                         with_env env3 (maybe_extract_mldefs tcmod)  in
                       (match uu____2114 with
                        | (extracted_defs,extract_time) ->
                            let uu____2145 =
                              FStar_Util.record_time
                                (fun uu____2160  ->
                                   FStar_Extraction_ML_Modul.extract_iface
                                     env3 tcmod)
                               in
                            (match uu____2145 with
                             | ((env4,extracted_iface),iface_extract_time) ->
                                 ({
                                    checked_module = tcmod;
                                    extracted_iface;
                                    mii;
                                    tc_time;
                                    extraction_time =
                                      (iface_extract_time + extract_time)
                                  }, extracted_defs, env4)))
                    in
                 let uu____2180 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                    in
                 if uu____2180
                 then
                   let uu____2191 = FStar_Parser_ParseIt.find_file fn  in
                   FStar_SMTEncoding_Solver.with_hints_db uu____2191
                     check_mod
                 else check_mod ()
              in
           let uu____2203 =
             let uu____2205 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____2205  in
           if uu____2203
           then
             let uu____2218 = load_module_from_cache env fn  in
             match uu____2218 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____2232 =
                     (let uu____2236 = FStar_Options.codegen ()  in
                      FStar_Option.isSome uu____2236) &&
                       (FStar_Options.cmi ())
                      in
                   if uu____2232
                   then
                     let uu____2240 =
                       let uu____2246 =
                         FStar_Util.format1
                           "Cross-module inlining expects all modules to be checked first; %s was not checked"
                           fn
                          in
                       (FStar_Errors.Error_UncheckedFile, uu____2246)  in
                     FStar_Errors.raise_err uu____2240
                   else ());
                  (let uu____2252 = tc_source_file ()  in
                   match uu____2252 with
                   | (tc_result,mllib,env1) ->
                       ((let uu____2279 =
                           (let uu____2283 = FStar_Errors.get_err_count ()
                               in
                            uu____2283 = (Prims.parse_int "0")) &&
                             ((FStar_Options.lax ()) ||
                                (FStar_Options.should_verify
                                   ((tc_result.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                            in
                         if uu____2279
                         then store_module_to_cache env1 fn tc_result
                         else ());
                        (tc_result, mllib, env1,
                          FStar_Pervasives_Native.None))))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.checked_module  in
                 ((let uu____2298 =
                     FStar_Options.dump_module
                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____2298
                   then
                     let uu____2301 =
                       FStar_Syntax_Print.modul_to_string tcmod  in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____2301
                   else ());
                  (let delta_tcenv tcmod1 tcenv =
                     let uu____2321 =
                       let uu____2326 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                           tc_result.mii
                           (FStar_TypeChecker_Normalize.erase_universes tcenv)
                          in
                       FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                         uu____2326
                        in
                     match uu____2321 with
                     | (uu____2346,tcenv1) ->
                         let uu____2348 =
                           FStar_TypeChecker_Tc.load_checked_module tcenv1
                             tcmod1
                            in
                         ((), uu____2348)
                      in
                   let mllib =
                     let uu____2352 =
                       ((let uu____2356 = FStar_Options.codegen ()  in
                         uu____2356 <> FStar_Pervasives_Native.None) &&
                          (FStar_Options.should_extract
                             (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                         &&
                         ((Prims.op_Negation
                             tcmod.FStar_Syntax_Syntax.is_interface)
                            ||
                            (let uu____2362 = FStar_Options.codegen ()  in
                             uu____2362 =
                               (FStar_Pervasives_Native.Some
                                  FStar_Options.Kremlin)))
                        in
                     if uu____2352
                     then
                       with_env env
                         (fun env1  ->
                            let env2 = apply_delta_env env1 delta1  in
                            let extract_defs tcmod1 env3 =
                              let uu____2400 =
                                with_tcenv_of_env env3 (delta_tcenv tcmod1)
                                 in
                              match uu____2400 with
                              | (uu____2412,env4) ->
                                  maybe_extract_mldefs tcmod1 env4
                               in
                            let uu____2414 = extract_defs tcmod env2  in
                            match uu____2414 with
                            | (extracted_defs,extraction_time) ->
                                extracted_defs)
                     else FStar_Pervasives_Native.None  in
                   let delta_env env1 =
                     let uu____2440 =
                       with_tcenv_of_env env1 (delta_tcenv tcmod)  in
                     match uu____2440 with
                     | (uu____2445,env2) ->
                         FStar_Extraction_ML_Modul.extend_with_iface env2
                           tc_result.extracted_iface
                      in
                   (tc_result, mllib, env,
                     (extend_delta_env delta1 delta_env))))
           else
             (let uu____2454 = tc_source_file ()  in
              match uu____2454 with
              | (tc_result,mllib,env1) ->
                  (tc_result, mllib, env1, FStar_Pervasives_Native.None)))
  
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
        let uu____2518 =
          tc_one_file env1 FStar_Pervasives_Native.None pre_fn fn  in
        match uu____2518 with
        | (tc_result,uu____2537,env2,delta1) ->
            let uu____2544 =
              let uu____2545 = apply_delta_env env2 delta1  in
              uu____2545.FStar_Extraction_ML_UEnv.env_tcenv  in
            (tc_result, uu____2544)
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____2570 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____2570 ["fsti"; "fsi"]))
        &&
        (let uu____2579 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____2579 ["fst"; "fs"])
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      delta_env ->
        (Prims.string Prims.list,tc_result Prims.list,FStar_Extraction_ML_Syntax.mllib
                                                        FStar_Pervasives_Native.option,
          uenv,delta_env) FStar_Pervasives_Native.tuple5)
  =
  fun remaining  ->
    fun env  ->
      fun delta_env  ->
        let uu____2628 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____2677 =
                tc_one_file env delta_env (FStar_Pervasives_Native.Some intf)
                  impl
                 in
              (match uu____2677 with
               | (m,mllib,env1,delta_env1) ->
                   (remaining1, ([m], mllib, env1, delta_env1)))
          | intf_or_impl::remaining1 ->
              let uu____2746 =
                tc_one_file env delta_env FStar_Pervasives_Native.None
                  intf_or_impl
                 in
              (match uu____2746 with
               | (m,mllib,env1,delta_env1) ->
                   (remaining1, ([m], mllib, env1, delta_env1)))
          | [] -> ([], ([], FStar_Pervasives_Native.None, env, delta_env))
           in
        match uu____2628 with
        | (remaining1,(nmods,mllib,env1,delta_env1)) ->
            (remaining1, nmods, mllib, env1, delta_env1)
  
let rec (tc_fold_interleave :
  (tc_result Prims.list,FStar_Extraction_ML_Syntax.mllib Prims.list,uenv,
    delta_env) FStar_Pervasives_Native.tuple4 ->
    Prims.string Prims.list ->
      (tc_result Prims.list,FStar_Extraction_ML_Syntax.mllib Prims.list,
        uenv,delta_env) FStar_Pervasives_Native.tuple4)
  =
  fun acc  ->
    fun remaining  ->
      let as_list uu___455_2950 =
        match uu___455_2950 with
        | FStar_Pervasives_Native.None  -> []
        | FStar_Pervasives_Native.Some l -> [l]  in
      match remaining with
      | [] -> acc
      | uu____2969 ->
          let uu____2973 = acc  in
          (match uu____2973 with
           | (mods,mllibs,env,delta_env) ->
               let uu____3010 =
                 tc_one_file_from_remaining remaining env delta_env  in
               (match uu____3010 with
                | (remaining1,nmods,mllib,env1,delta_env1) ->
                    tc_fold_interleave
                      ((FStar_List.append mods nmods),
                        (FStar_List.append mllibs (as_list mllib)), env1,
                        delta_env1) remaining1))
  
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      (tc_result Prims.list,uenv,(uenv -> uenv)
                                   FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun filenames  ->
    fun dep_graph1  ->
      (let uu____3098 = FStar_Options.debug_any ()  in
       if uu____3098
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____3106 =
             let uu____3108 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____3108  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____3106))
       else ());
      (let env =
         let uu____3124 = init_env dep_graph1  in
         FStar_Extraction_ML_UEnv.mkContext uu____3124  in
       let uu____3125 =
         tc_fold_interleave ([], [], env, FStar_Pervasives_Native.None)
           filenames
          in
       match uu____3125 with
       | (all_mods,mllibs,env1,delta1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____3177 =
                 with_tcenv_of_env env2
                   (fun tcenv  ->
                      (let uu____3186 =
                         (FStar_Options.interactive ()) &&
                           (let uu____3189 = FStar_Errors.get_err_count ()
                               in
                            uu____3189 = (Prims.parse_int "0"))
                          in
                       if uu____3186
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv))
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____3177  in
             (all_mods, env1, (extend_delta_env delta1 solver_refresh)))))
  