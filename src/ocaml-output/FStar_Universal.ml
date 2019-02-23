open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "8") 
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
      let uu____76026 = f tcenv.FStar_TypeChecker_Env.dsenv  in
      match uu____76026 with
      | (a,dsenv1) ->
          (a,
            (let uu___713_76040 = tcenv  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___713_76040.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___713_76040.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___713_76040.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___713_76040.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___713_76040.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___713_76040.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___713_76040.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___713_76040.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___713_76040.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___713_76040.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___713_76040.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___713_76040.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___713_76040.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___713_76040.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___713_76040.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___713_76040.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___713_76040.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___713_76040.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___713_76040.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___713_76040.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___713_76040.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___713_76040.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___713_76040.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___713_76040.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___713_76040.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___713_76040.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___713_76040.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___713_76040.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___713_76040.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___713_76040.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___713_76040.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___713_76040.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___713_76040.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___713_76040.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___713_76040.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___713_76040.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___713_76040.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___713_76040.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___713_76040.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___713_76040.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___713_76040.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___713_76040.FStar_TypeChecker_Env.nbe)
             }))
  
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e  ->
    fun f  ->
      let uu____76076 = f e.FStar_Extraction_ML_UEnv.env_tcenv  in
      match uu____76076 with
      | (a,t') ->
          (a,
            (let uu___721_76088 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = t';
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___721_76088.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___721_76088.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___721_76088.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___721_76088.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e  ->
    fun f  ->
      let uu____76121 =
        with_dsenv_of_tcenv e.FStar_Extraction_ML_UEnv.env_tcenv f  in
      match uu____76121 with
      | (a,tcenv) ->
          (a,
            (let uu___729_76137 = e  in
             {
               FStar_Extraction_ML_UEnv.env_tcenv = tcenv;
               FStar_Extraction_ML_UEnv.env_bindings =
                 (uu___729_76137.FStar_Extraction_ML_UEnv.env_bindings);
               FStar_Extraction_ML_UEnv.tydefs =
                 (uu___729_76137.FStar_Extraction_ML_UEnv.tydefs);
               FStar_Extraction_ML_UEnv.type_names =
                 (uu___729_76137.FStar_Extraction_ML_UEnv.type_names);
               FStar_Extraction_ML_UEnv.currentModule =
                 (uu___729_76137.FStar_Extraction_ML_UEnv.currentModule)
             }))
  
let (push_env : uenv -> uenv) =
  fun env  ->
    let uu____76144 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____76152 =
             FStar_TypeChecker_Env.push
               env.FStar_Extraction_ML_UEnv.env_tcenv "top-level: push_env"
              in
           ((), uu____76152))
       in
    FStar_Pervasives_Native.snd uu____76144
  
let (pop_env : uenv -> uenv) =
  fun env  ->
    let uu____76160 =
      with_tcenv_of_env env
        (fun tcenv  ->
           let uu____76168 =
             FStar_TypeChecker_Env.pop tcenv "top-level: pop_env"  in
           ((), uu____76168))
       in
    FStar_Pervasives_Native.snd uu____76160
  
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env  ->
    fun f  ->
      let env1 = push_env env  in
      let res = f env1  in let uu____76195 = pop_env env1  in res
  
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
        let uu____76234 = FStar_Parser_Driver.parse_file fn  in
        match uu____76234 with
        | (ast,uu____76251) ->
            let uu____76266 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____76279 = FStar_Parser_Driver.parse_file pre_fn1
                     in
                  (match uu____76279 with
                   | (pre_ast,uu____76296) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____76317),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____76330 =
                              let uu____76335 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              with_dsenv_of_env env uu____76335  in
                            (match uu____76330 with
                             | (uu____76348,env1) ->
                                 let uu____76350 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 with_dsenv_of_env env1 uu____76350)
                        | uu____76360 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____76266 with
             | (ast1,env1) ->
                 let uu____76377 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 with_dsenv_of_env env1 uu____76377)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____76393 = FStar_Options.lax ()  in
      if uu____76393
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___773_76398 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___773_76398.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___773_76398.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___773_76398.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___773_76398.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___773_76398.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_sig =
             (uu___773_76398.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___773_76398.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___773_76398.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___773_76398.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____76400 =
        let uu____76415 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____76415  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____76400
       in
    let env1 =
      let uu___777_76419 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___777_76419.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___777_76419.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___777_76419.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___777_76419.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___777_76419.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___777_76419.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___777_76419.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___777_76419.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___777_76419.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___777_76419.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___777_76419.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___777_76419.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___777_76419.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___777_76419.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___777_76419.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___777_76419.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___777_76419.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___777_76419.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___777_76419.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___777_76419.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___777_76419.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___777_76419.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___777_76419.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___777_76419.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___777_76419.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___777_76419.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___777_76419.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___777_76419.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___777_76419.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___777_76419.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___777_76419.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___777_76419.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___777_76419.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___777_76419.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___777_76419.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___777_76419.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___777_76419.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___777_76419.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___777_76419.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___777_76419.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___777_76419.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___777_76419.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___780_76421 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___780_76421.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___780_76421.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___780_76421.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___780_76421.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___780_76421.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___780_76421.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___780_76421.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___780_76421.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___780_76421.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___780_76421.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___780_76421.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___780_76421.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___780_76421.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___780_76421.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___780_76421.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___780_76421.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___780_76421.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___780_76421.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___780_76421.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___780_76421.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___780_76421.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___780_76421.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___780_76421.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___780_76421.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___780_76421.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___780_76421.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___780_76421.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___780_76421.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___780_76421.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___780_76421.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___780_76421.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___780_76421.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___780_76421.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___780_76421.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___780_76421.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___780_76421.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___780_76421.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___780_76421.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___780_76421.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___780_76421.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___780_76421.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___780_76421.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___783_76423 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___783_76423.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___783_76423.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___783_76423.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___783_76423.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___783_76423.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___783_76423.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___783_76423.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___783_76423.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___783_76423.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___783_76423.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___783_76423.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___783_76423.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___783_76423.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___783_76423.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___783_76423.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___783_76423.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___783_76423.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___783_76423.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___783_76423.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___783_76423.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___783_76423.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___783_76423.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___783_76423.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___783_76423.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___783_76423.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___783_76423.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___783_76423.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___783_76423.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___783_76423.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___783_76423.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___783_76423.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___783_76423.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___783_76423.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___783_76423.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___783_76423.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___783_76423.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___783_76423.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___783_76423.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___783_76423.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___783_76423.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___783_76423.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___783_76423.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___786_76425 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___786_76425.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___786_76425.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___786_76425.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___786_76425.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___786_76425.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___786_76425.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___786_76425.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___786_76425.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___786_76425.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___786_76425.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___786_76425.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___786_76425.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___786_76425.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___786_76425.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___786_76425.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___786_76425.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___786_76425.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___786_76425.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___786_76425.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___786_76425.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___786_76425.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___786_76425.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___786_76425.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___786_76425.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___786_76425.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___786_76425.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___786_76425.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___786_76425.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___786_76425.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___786_76425.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___786_76425.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___786_76425.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___786_76425.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___786_76425.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___786_76425.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___786_76425.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___786_76425.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___786_76425.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___786_76425.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___786_76425.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___786_76425.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___786_76425.FStar_TypeChecker_Env.nbe)
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
          let uu____76460 =
            let uu____76462 =
              let uu____76464 = FStar_Options.file_list ()  in
              FStar_List.hd uu____76464  in
            FStar_Parser_Dep.lowercase_module_name uu____76462  in
          let uu____76469 =
            let uu____76471 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____76471  in
          uu____76460 = uu____76469  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____76480,{ FStar_Parser_AST.d = uu____76481;
                             FStar_Parser_AST.drange = d;
                             FStar_Parser_AST.doc = uu____76483;
                             FStar_Parser_AST.quals = uu____76484;
                             FStar_Parser_AST.attrs = uu____76485;_}::uu____76486)
              -> d
          | FStar_Parser_AST.Interface
              (uu____76493,{ FStar_Parser_AST.d = uu____76494;
                             FStar_Parser_AST.drange = d;
                             FStar_Parser_AST.doc = uu____76496;
                             FStar_Parser_AST.quals = uu____76497;
                             FStar_Parser_AST.attrs = uu____76498;_}::uu____76499,uu____76500)
              -> d
          | uu____76509 -> FStar_Range.dummyRange  in
        let uu____76510 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____76510 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____76522 =
              let uu____76527 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____76527  in
            (match uu____76522 with
             | (ast_modul1,env1) ->
                 let uu____76552 =
                   let uu____76557 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_dsenv_of_tcenv env1) uu____76557
                    in
                 (match uu____76552 with
                  | (modul,env2) ->
                      ((let uu____76582 =
                          let uu____76584 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____76584  in
                        if uu____76582
                        then
                          let msg =
                            let uu____76589 =
                              let uu____76591 =
                                let uu____76593 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____76593  in
                              FStar_Parser_Dep.module_name_of_file
                                uu____76591
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____76589
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____76602 =
                          let uu____76613 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____76613
                          then ((modul, []), env2)
                          else
                            (let uu____76636 =
                               FStar_TypeChecker_Tc.tc_partial_modul env2
                                 modul
                                in
                             match uu____76636 with | (m,i,e) -> ((m, i), e))
                           in
                        match uu____76602 with
                        | ((modul1,uu____76677),env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____76700 = FStar_List.hd ast_decls  in
                 (match uu____76700 with
                  | { FStar_Parser_AST.d = uu____76707;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____76709;
                      FStar_Parser_AST.quals = uu____76710;
                      FStar_Parser_AST.attrs = uu____76711;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____76723 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____76741 =
                            let uu____76748 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                              uu____76748
                             in
                          match uu____76741 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____76723 with
                  | (env1,ast_decls_l) ->
                      let uu____76802 =
                        let uu____76807 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_dsenv_of_tcenv env1)
                          uu____76807
                         in
                      (match uu____76802 with
                       | (sigelts,env2) ->
                           let uu____76831 =
                             let uu____76840 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____76840
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____76831 with
                            | (modul1,uu____76862,env3) ->
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
           (l,decls,uu____76886)),uu____76887)
          ->
          let uu____76910 =
            let uu____76915 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_dsenv_of_tcenv env) uu____76915  in
          FStar_Pervasives_Native.snd uu____76910
      | FStar_Parser_ParseIt.ASTFragment uu____76931 ->
          let uu____76943 =
            let uu____76949 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____76949)  in
          FStar_Errors.raise_err uu____76943
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____76959 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
  
type cache_t =
  (Prims.int * (Prims.string * Prims.string) Prims.list * Prims.string *
    FStar_Parser_Dep.parsing_data * tc_result)
let (load_value_from_cache :
  Prims.string -> (cache_t FStar_Pervasives_Native.option * Prims.string)) =
  fun cache_file  ->
    let uu____77003 = FStar_Util.load_value_from_file cache_file  in
    match uu____77003 with
    | FStar_Pervasives_Native.None  ->
        (FStar_Pervasives_Native.None, "Corrupt")
    | FStar_Pervasives_Native.Some cache_data ->
        let uu____77118 = cache_data  in
        (match uu____77118 with
         | (vnum,uu____77147,uu____77148,uu____77149,uu____77150) ->
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
        (fun uu___907_77224  ->
           match () with
           | () ->
               let uu____77228 = FStar_Parser_Dep.cache_file_name file_name
                  in
               FStar_All.pipe_right uu____77228
                 (fun _77235  -> FStar_Pervasives_Native.Some _77235)) ()
      with | uu___906_77237 -> FStar_Pervasives_Native.None  in
    if cache_file = FStar_Pervasives_Native.None
    then FStar_Pervasives_Native.None
    else
      (let uu____77251 =
         let uu____77279 = FStar_All.pipe_right cache_file FStar_Util.must
            in
         FStar_All.pipe_right uu____77279 load_value_from_cache  in
       match uu____77251 with
       | (FStar_Pervasives_Native.None ,uu____77316) ->
           FStar_Pervasives_Native.None
       | (FStar_Pervasives_Native.Some
          (uu____77361,uu____77362,dig,pd,uu____77365),uu____77366) ->
           let uu____77431 =
             let uu____77433 = FStar_Util.digest_of_file file_name  in
             dig <> uu____77433  in
           if uu____77431
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
    let uu____77536 = load_value_from_cache cache_file  in
    match uu____77536 with
    | (FStar_Pervasives_Native.None ,msg) -> FStar_Util.Inl msg
    | (FStar_Pervasives_Native.Some
       (uu____77555,digest,uu____77557,uu____77558,tc_result),uu____77560) ->
        let uu____77585 =
          let uu____77596 = FStar_TypeChecker_Env.dep_graph env  in
          FStar_Parser_Dep.hash_dependences uu____77596 source_file
            cache_file
           in
        (match uu____77585 with
         | FStar_Pervasives_Native.Some digest' ->
             if digest = digest'
             then FStar_Util.Inr tc_result
             else
               ((let uu____77637 = FStar_Options.debug_any ()  in
                 if uu____77637
                 then
                   ((let uu____77641 =
                       FStar_Util.string_of_int (FStar_List.length digest')
                        in
                     let uu____77649 = FStar_Parser_Dep.print_digest digest'
                        in
                     let uu____77651 =
                       FStar_Util.string_of_int (FStar_List.length digest)
                        in
                     let uu____77659 = FStar_Parser_Dep.print_digest digest
                        in
                     FStar_Util.print4
                       "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                       uu____77641 uu____77649 uu____77651 uu____77659);
                    if
                      (FStar_List.length digest) =
                        (FStar_List.length digest')
                    then
                      FStar_List.iter2
                        (fun uu____77695  ->
                           fun uu____77696  ->
                             match (uu____77695, uu____77696) with
                             | ((x,y),(x',y')) ->
                                 if (x <> x') || (y <> y')
                                 then
                                   let uu____77748 =
                                     FStar_Parser_Dep.print_digest [(x, y)]
                                      in
                                   let uu____77764 =
                                     FStar_Parser_Dep.print_digest [(x', y')]
                                      in
                                   FStar_Util.print2
                                     "Differ at: Expected %s\n Got %s\n"
                                     uu____77748 uu____77764
                                 else ()) digest digest'
                    else ())
                 else ());
                FStar_Util.Inl "Stale")
         | uu____77789 -> FStar_Util.Inl "Unable to compute digest of")
     in
  fun env  ->
    fun fn  ->
      let load_it uu____77812 =
        let cache_file = FStar_Parser_Dep.cache_file_name fn  in
        let fail1 maybe_warn cache_file1 =
          invalidate_cache ();
          (match maybe_warn with
           | FStar_Pervasives_Native.None  -> ()
           | FStar_Pervasives_Native.Some tag ->
               let uu____77839 =
                 let uu____77840 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 let uu____77843 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 FStar_Range.mk_range fn uu____77840 uu____77843  in
               let uu____77846 =
                 let uu____77852 =
                   FStar_Util.format3
                     "%s cache file %s; will recheck %s and all subsequent files"
                     tag cache_file1 fn
                    in
                 (FStar_Errors.Warning_CachedFile, uu____77852)  in
               FStar_Errors.log_issue uu____77839 uu____77846)
           in
        let uu____77856 = FStar_ST.op_Bang some_cache_invalid  in
        match uu____77856 with
        | FStar_Pervasives_Native.Some uu____77906 ->
            FStar_Pervasives_Native.None
        | uu____77907 ->
            if Prims.op_Negation (FStar_Util.file_exists cache_file)
            then FStar_Pervasives_Native.None
            else
              (let uu____77915 =
                 load1 env.FStar_Extraction_ML_UEnv.env_tcenv fn cache_file
                  in
               match uu____77915 with
               | FStar_Util.Inl msg ->
                   (fail1 (FStar_Pervasives_Native.Some msg) cache_file;
                    FStar_Pervasives_Native.None)
               | FStar_Util.Inr res -> FStar_Pervasives_Native.Some res)
         in
      FStar_Options.profile load_it
        (fun res  ->
           let msg = if FStar_Option.isSome res then "ok" else "failed"  in
           let uu____77946 = FStar_Parser_Dep.cache_file_name fn  in
           FStar_Util.format2 "Loading checked file %s ... %s" uu____77946
             msg)
  
let (store_module_to_cache :
  uenv -> Prims.string -> FStar_Parser_Dep.parsing_data -> tc_result -> unit)
  =
  fun env  ->
    fun fn  ->
      fun parsing_data  ->
        fun tc_result  ->
          let uu____77972 =
            (FStar_Options.cache_checked_modules ()) &&
              (let uu____77975 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____77975)
             in
          if uu____77972
          then
            let cache_file = FStar_Parser_Dep.cache_file_name fn  in
            let digest =
              let uu____77991 =
                FStar_TypeChecker_Env.dep_graph
                  env.FStar_Extraction_ML_UEnv.env_tcenv
                 in
              FStar_Parser_Dep.hash_dependences uu____77991 fn cache_file  in
            match digest with
            | FStar_Pervasives_Native.Some hashes ->
                let tc_result1 =
                  let uu___994_78010 = tc_result  in
                  {
                    checked_module = (uu___994_78010.checked_module);
                    mii = (uu___994_78010.mii);
                    smt_decls = (uu___994_78010.smt_decls);
                    tc_time = (Prims.parse_int "0");
                    extraction_time = (uu___994_78010.extraction_time)
                  }  in
                let uu____78012 =
                  let uu____78013 = FStar_Util.digest_of_file fn  in
                  (cache_version_number, hashes, uu____78013, parsing_data,
                    tc_result1)
                   in
                store_value_to_cache cache_file uu____78012
            | uu____78025 ->
                let uu____78036 =
                  let uu____78037 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  let uu____78040 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  FStar_Range.mk_range fn uu____78037 uu____78040  in
                let uu____78043 =
                  let uu____78049 =
                    FStar_Util.format1
                      "%s was not written, since some of its dependences were not also checked"
                      cache_file
                     in
                  (FStar_Errors.Warning_FileNotWritten, uu____78049)  in
                FStar_Errors.log_issue uu____78036 uu____78043
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
            ((fun e  -> let uu____78133 = f1 e  in g uu____78133))
  
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
        | uu____78157 -> failwith "Unrecognized option"  in
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
           | (name,uu____78182)::[] ->
               let uu____78185 =
                 FStar_Options.prepend_output_dir (Prims.op_Hat name ext)  in
               FStar_Util.save_value_to_file uu____78185 bin
           | uu____78187 ->
               let uu____78190 = FStar_Options.prepend_output_dir "out.krml"
                  in
               FStar_Util.save_value_to_file uu____78190 bin)
      | uu____78193 -> failwith "Unrecognized option"
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
            (let post_smt_encoding uu____78261 =
               FStar_SMTEncoding_Z3.refresh ();
               (let uu____78263 =
                  let uu____78265 = FStar_Options.interactive ()  in
                  Prims.op_Negation uu____78265  in
                if uu____78263
                then
                  let uu____78268 =
                    FStar_Options.restore_cmd_line_options true  in
                  FStar_All.pipe_right uu____78268 (fun a1  -> ())
                else ())
                in
             let maybe_extract_mldefs tcmod env1 =
               let uu____78290 =
                 (let uu____78294 = FStar_Options.codegen ()  in
                  uu____78294 = FStar_Pervasives_Native.None) ||
                   (let uu____78300 =
                      FStar_Options.should_extract
                        (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                       in
                    Prims.op_Negation uu____78300)
                  in
               if uu____78290
               then (FStar_Pervasives_Native.None, (Prims.parse_int "0"))
               else
                 FStar_Util.record_time
                   (fun uu____78322  ->
                      let uu____78323 =
                        FStar_Extraction_ML_Modul.extract env1 tcmod  in
                      match uu____78323 with | (uu____78332,defs) -> defs)
                in
             let maybe_extract_ml_iface tcmod env1 =
               let uu____78354 =
                 let uu____78356 = FStar_Options.codegen ()  in
                 uu____78356 = FStar_Pervasives_Native.None  in
               if uu____78354
               then (env1, (Prims.parse_int "0"))
               else
                 (let uu____78371 =
                    FStar_Util.record_time
                      (fun uu____78386  ->
                         FStar_Extraction_ML_Modul.extract_iface env1 tcmod)
                     in
                  match uu____78371 with
                  | ((env2,_extracted_iface),iface_extract_time) ->
                      (env2, iface_extract_time))
                in
             let tc_source_file uu____78415 =
               let env1 = apply_delta_env env delta1  in
               let uu____78419 = parse env1 pre_fn fn  in
               match uu____78419 with
               | (fmod,env2) ->
                   let mii =
                     FStar_Syntax_DsEnv.inclusion_info
                       (env2.FStar_Extraction_ML_UEnv.env_tcenv).FStar_TypeChecker_Env.dsenv
                       fmod.FStar_Syntax_Syntax.name
                      in
                   let check_mod uu____78448 =
                     let uu____78449 =
                       FStar_Util.record_time
                         (fun uu____78484  ->
                            with_tcenv_of_env env2
                              (fun tcenv  ->
                                 (match tcenv.FStar_TypeChecker_Env.gamma
                                  with
                                  | [] -> ()
                                  | uu____78503 ->
                                      failwith
                                        "Impossible: gamma contains leaked names");
                                 (let uu____78507 =
                                    FStar_TypeChecker_Tc.check_module tcenv
                                      fmod (FStar_Util.is_some pre_fn)
                                     in
                                  match uu____78507 with
                                  | (modul,env3) ->
                                      let smt_decls =
                                        let uu____78536 =
                                          let uu____78538 =
                                            FStar_Options.lax ()  in
                                          Prims.op_Negation uu____78538  in
                                        if uu____78536
                                        then
                                          let smt_decls =
                                            FStar_SMTEncoding_Encode.encode_modul
                                              env3 modul
                                             in
                                          (post_smt_encoding (); smt_decls)
                                        else ([], [])  in
                                      ((modul, smt_decls), env3))))
                        in
                     match uu____78449 with
                     | (((tcmod,smt_decls),env3),tc_time) ->
                         let uu____78625 =
                           with_env env3 (maybe_extract_mldefs tcmod)  in
                         (match uu____78625 with
                          | (extracted_defs,extract_time) ->
                              let uu____78656 =
                                with_env env3 (maybe_extract_ml_iface tcmod)
                                 in
                              (match uu____78656 with
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
                   let uu____78681 =
                     (FStar_Options.should_verify
                        (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                       &&
                       ((FStar_Options.record_hints ()) ||
                          (FStar_Options.use_hints ()))
                      in
                   if uu____78681
                   then
                     let uu____78692 = FStar_Parser_ParseIt.find_file fn  in
                     FStar_SMTEncoding_Solver.with_hints_db uu____78692
                       check_mod
                   else check_mod ()
                in
             let uu____78704 =
               let uu____78706 = FStar_Options.cache_off ()  in
               Prims.op_Negation uu____78706  in
             if uu____78704
             then
               let uu____78719 = load_module_from_cache env fn  in
               match uu____78719 with
               | FStar_Pervasives_Native.None  ->
                   ((let uu____78733 =
                       let uu____78735 =
                         FStar_Parser_Dep.module_name_of_file fn  in
                       FStar_Options.should_be_already_cached uu____78735  in
                     if uu____78733
                     then
                       let uu____78738 =
                         let uu____78744 =
                           FStar_Util.format1
                             "Expected %s to already be checked" fn
                            in
                         (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                           uu____78744)
                          in
                       FStar_Errors.raise_err uu____78738
                     else ());
                    (let uu____78751 =
                       (let uu____78755 = FStar_Options.codegen ()  in
                        FStar_Option.isSome uu____78755) &&
                         (FStar_Options.cmi ())
                        in
                     if uu____78751
                     then
                       let uu____78759 =
                         let uu____78765 =
                           FStar_Util.format1
                             "Cross-module inlining expects all modules to be checked first; %s was not checked"
                             fn
                            in
                         (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                           uu____78765)
                          in
                       FStar_Errors.raise_err uu____78759
                     else ());
                    (let uu____78771 = tc_source_file ()  in
                     match uu____78771 with
                     | (tc_result,mllib,env1) ->
                         ((let uu____78798 =
                             (let uu____78802 = FStar_Errors.get_err_count ()
                                 in
                              uu____78802 = (Prims.parse_int "0")) &&
                               ((FStar_Options.lax ()) ||
                                  (FStar_Options.should_verify
                                     ((tc_result.checked_module).FStar_Syntax_Syntax.name).FStar_Ident.str))
                              in
                           if uu____78798
                           then
                             store_module_to_cache env1 fn parsing_data
                               tc_result
                           else ());
                          (tc_result, mllib, env1,
                            FStar_Pervasives_Native.None))))
               | FStar_Pervasives_Native.Some tc_result ->
                   let tcmod = tc_result.checked_module  in
                   let smt_decls = tc_result.smt_decls  in
                   ((let uu____78824 =
                       FStar_Options.dump_module
                         (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                        in
                     if uu____78824
                     then
                       let uu____78827 =
                         FStar_Syntax_Print.modul_to_string tcmod  in
                       FStar_Util.print1 "Module after type checking:\n%s\n"
                         uu____78827
                     else ());
                    (let delta_tcenv tcmod1 tcenv =
                       let uu____78847 =
                         let uu____78852 =
                           FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                             tc_result.mii
                             (FStar_TypeChecker_Normalize.erase_universes
                                tcenv)
                            in
                         FStar_All.pipe_left (with_dsenv_of_tcenv tcenv)
                           uu____78852
                          in
                       match uu____78847 with
                       | (uu____78872,tcenv1) ->
                           let env1 =
                             FStar_TypeChecker_Tc.load_checked_module tcenv1
                               tcmod1
                              in
                           ((let uu____78876 =
                               let uu____78878 = FStar_Options.lax ()  in
                               Prims.op_Negation uu____78878  in
                             if uu____78876
                             then
                               (FStar_SMTEncoding_Encode.encode_modul_from_cache
                                  env1 tcmod1.FStar_Syntax_Syntax.name
                                  smt_decls;
                                post_smt_encoding ())
                             else ());
                            ((), env1))
                        in
                     let mllib =
                       let uu____78887 =
                         ((let uu____78891 = FStar_Options.codegen ()  in
                           uu____78891 <> FStar_Pervasives_Native.None) &&
                            (FStar_Options.should_extract
                               (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                           &&
                           ((Prims.op_Negation
                               tcmod.FStar_Syntax_Syntax.is_interface)
                              ||
                              (let uu____78897 = FStar_Options.codegen ()  in
                               uu____78897 =
                                 (FStar_Pervasives_Native.Some
                                    FStar_Options.Kremlin)))
                          in
                       if uu____78887
                       then
                         with_env env
                           (fun env1  ->
                              let env2 = apply_delta_env env1 delta1  in
                              let extract_defs tcmod1 env3 =
                                let uu____78935 =
                                  with_tcenv_of_env env3 (delta_tcenv tcmod1)
                                   in
                                match uu____78935 with
                                | (uu____78947,env4) ->
                                    maybe_extract_mldefs tcmod1 env4
                                 in
                              let uu____78949 = extract_defs tcmod env2  in
                              match uu____78949 with
                              | (extracted_defs,extraction_time) ->
                                  extracted_defs)
                       else FStar_Pervasives_Native.None  in
                     let delta_env env1 =
                       FStar_Options.profile
                         (fun uu____78982  ->
                            let uu____78983 =
                              with_tcenv_of_env env1 (delta_tcenv tcmod)  in
                            match uu____78983 with
                            | (uu____78988,env2) ->
                                let uu____78990 =
                                  with_env env2
                                    (maybe_extract_ml_iface tcmod)
                                   in
                                (match uu____78990 with
                                 | (env3,_time) -> env3))
                         (fun uu____79006  ->
                            FStar_Util.format1
                              "Extending environment with module %s"
                              (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                        in
                     (tc_result, mllib, env,
                       (extend_delta_env delta1 delta_env))))
             else
               (let uu____79015 = tc_source_file ()  in
                match uu____79015 with
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
          let uu____79084 =
            tc_one_file env1 FStar_Pervasives_Native.None pre_fn fn
              parsing_data
             in
          match uu____79084 with
          | (tc_result,uu____79103,env2,delta1) ->
              let uu____79110 =
                let uu____79111 = apply_delta_env env2 delta1  in
                uu____79111.FStar_Extraction_ML_UEnv.env_tcenv  in
              (tc_result, uu____79110)
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____79136 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____79136 ["fsti"; "fsi"]))
        &&
        (let uu____79145 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____79145 ["fst"; "fs"])
  
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
          let uu____79199 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____79248 =
                  let uu____79259 =
                    FStar_All.pipe_right impl
                      (FStar_Parser_Dep.parsing_data_of deps)
                     in
                  tc_one_file env delta_env
                    (FStar_Pervasives_Native.Some intf) impl uu____79259
                   in
                (match uu____79248 with
                 | (m,mllib,env1,delta_env1) ->
                     (remaining1, ([m], mllib, env1, delta_env1)))
            | intf_or_impl::remaining1 ->
                let uu____79319 =
                  let uu____79330 =
                    FStar_All.pipe_right intf_or_impl
                      (FStar_Parser_Dep.parsing_data_of deps)
                     in
                  tc_one_file env delta_env FStar_Pervasives_Native.None
                    intf_or_impl uu____79330
                   in
                (match uu____79319 with
                 | (m,mllib,env1,delta_env1) ->
                     (remaining1, ([m], mllib, env1, delta_env1)))
            | [] -> ([], ([], FStar_Pervasives_Native.None, env, delta_env))
             in
          match uu____79199 with
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
        let as_list uu___690_79530 =
          match uu___690_79530 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some l -> [l]  in
        match remaining with
        | [] -> acc
        | uu____79549 ->
            let uu____79553 = acc  in
            (match uu____79553 with
             | (mods,mllibs,env,delta_env) ->
                 let uu____79590 =
                   tc_one_file_from_remaining remaining env delta_env deps
                    in
                 (match uu____79590 with
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
      (let uu____79678 = FStar_Options.debug_any ()  in
       if uu____79678
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____79686 =
             let uu____79688 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____79688  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____79686))
       else ());
      (let env =
         let uu____79704 = init_env dep_graph1  in
         FStar_Extraction_ML_UEnv.mkContext uu____79704  in
       let uu____79705 =
         tc_fold_interleave dep_graph1
           ([], [], env, FStar_Pervasives_Native.None) filenames
          in
       match uu____79705 with
       | (all_mods,mllibs,env1,delta1) ->
           (emit mllibs;
            (let solver_refresh env2 =
               let uu____79757 =
                 with_tcenv_of_env env2
                   (fun tcenv  ->
                      (let uu____79766 =
                         (FStar_Options.interactive ()) &&
                           (let uu____79769 = FStar_Errors.get_err_count ()
                               in
                            uu____79769 = (Prims.parse_int "0"))
                          in
                       if uu____79766
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv))
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.snd uu____79757
                in
             (all_mods, env1, (extend_delta_env delta1 solver_refresh)))))
  