open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "4") 
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul ->
    (Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2)
  =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
  
let with_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_Syntax_DsEnv.withenv ->
        ('a,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____41 = f env.FStar_TypeChecker_Env.dsenv  in
      match uu____41 with
      | (a,dsenv1) ->
          (a,
            (let uu___416_55 = env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___416_55.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___416_55.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___416_55.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___416_55.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___416_55.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___416_55.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___416_55.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___416_55.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___416_55.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___416_55.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___416_55.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___416_55.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___416_55.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___416_55.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___416_55.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___416_55.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___416_55.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___416_55.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___416_55.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___416_55.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___416_55.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___416_55.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___416_55.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___416_55.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___416_55.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___416_55.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___416_55.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___416_55.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___416_55.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___416_55.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___416_55.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___416_55.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___416_55.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___416_55.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___416_55.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___416_55.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___416_55.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___416_55.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___416_55.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___416_55.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___416_55.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.nbe =
                 (uu___416_55.FStar_TypeChecker_Env.nbe)
             }))
  
let (parse :
  FStar_TypeChecker_Env.env ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____83 = FStar_Parser_Driver.parse_file fn  in
        match uu____83 with
        | (ast,uu____99) ->
            let uu____112 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____122 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____122 with
                   | (pre_ast,uu____138) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____157),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____168 =
                              let uu____173 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              FStar_All.pipe_left (with_tcenv env) uu____173
                               in
                            (match uu____168 with
                             | (uu____193,env1) ->
                                 let uu____195 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 FStar_All.pipe_left (with_tcenv env1)
                                   uu____195)
                        | uu____211 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____112 with
             | (ast1,env1) ->
                 let uu____226 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 FStar_All.pipe_left (with_tcenv env1) uu____226)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____248 = FStar_Options.lax ()  in
      if uu____248
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___417_250 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___417_250.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___417_250.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___417_250.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.snapshot =
             (uu___417_250.FStar_TypeChecker_Env.snapshot);
           FStar_TypeChecker_Env.rollback =
             (uu___417_250.FStar_TypeChecker_Env.rollback);
           FStar_TypeChecker_Env.encode_modul =
             (uu___417_250.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___417_250.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___417_250.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___417_250.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___417_250.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      let uu____252 =
        let uu____267 = FStar_Tactics_Interpreter.primitive_steps ()  in
        FStar_TypeChecker_NBE.normalize uu____267  in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid uu____252
       in
    let env1 =
      let uu___418_271 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___418_271.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___418_271.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___418_271.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___418_271.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___418_271.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___418_271.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___418_271.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___418_271.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___418_271.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___418_271.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___418_271.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___418_271.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___418_271.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___418_271.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___418_271.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___418_271.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___418_271.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___418_271.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___418_271.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___418_271.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___418_271.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___418_271.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___418_271.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___418_271.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___418_271.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___418_271.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___418_271.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___418_271.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___418_271.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___418_271.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___418_271.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___418_271.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___418_271.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___418_271.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___418_271.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___418_271.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___418_271.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___418_271.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___418_271.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___418_271.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___418_271.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___418_271.FStar_TypeChecker_Env.nbe)
      }  in
    let env2 =
      let uu___419_273 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___419_273.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___419_273.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___419_273.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___419_273.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___419_273.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___419_273.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___419_273.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___419_273.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___419_273.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___419_273.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___419_273.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___419_273.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___419_273.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___419_273.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___419_273.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___419_273.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___419_273.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___419_273.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___419_273.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___419_273.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___419_273.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___419_273.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___419_273.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___419_273.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___419_273.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___419_273.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___419_273.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___419_273.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___419_273.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___419_273.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___419_273.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___419_273.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___419_273.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___419_273.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___419_273.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___419_273.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.postprocess =
          (uu___419_273.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___419_273.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___419_273.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___419_273.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___419_273.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___419_273.FStar_TypeChecker_Env.nbe)
      }  in
    let env3 =
      let uu___420_275 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___420_275.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___420_275.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___420_275.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___420_275.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___420_275.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___420_275.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___420_275.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___420_275.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___420_275.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___420_275.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___420_275.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___420_275.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___420_275.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___420_275.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___420_275.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___420_275.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___420_275.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___420_275.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___420_275.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___420_275.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___420_275.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___420_275.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___420_275.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___420_275.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___420_275.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___420_275.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___420_275.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___420_275.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___420_275.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___420_275.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___420_275.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___420_275.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___420_275.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___420_275.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___420_275.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___420_275.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___420_275.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          FStar_Tactics_Interpreter.postprocess;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___420_275.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___420_275.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___420_275.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___420_275.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___420_275.FStar_TypeChecker_Env.nbe)
      }  in
    let env4 =
      let uu___421_277 = env3  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___421_277.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___421_277.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___421_277.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___421_277.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___421_277.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___421_277.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___421_277.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___421_277.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___421_277.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___421_277.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___421_277.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___421_277.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___421_277.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___421_277.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___421_277.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___421_277.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___421_277.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___421_277.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___421_277.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___421_277.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___421_277.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___421_277.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___421_277.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___421_277.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___421_277.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___421_277.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___421_277.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___421_277.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___421_277.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___421_277.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___421_277.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___421_277.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___421_277.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___421_277.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___421_277.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___421_277.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___421_277.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___421_277.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___421_277.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___421_277.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___421_277.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___421_277.FStar_TypeChecker_Env.nbe)
      }  in
    (env4.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env4; env4
  
let (tc_one_fragment :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun curmod  ->
    fun env  ->
      fun frag  ->
        let acceptable_mod_name modul =
          let uu____310 =
            let uu____311 =
              let uu____312 = FStar_Options.file_list ()  in
              FStar_List.hd uu____312  in
            FStar_Parser_Dep.lowercase_module_name uu____311  in
          let uu____315 =
            let uu____316 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____316  in
          uu____310 = uu____315  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____323,{ FStar_Parser_AST.d = uu____324;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____326;
                           FStar_Parser_AST.quals = uu____327;
                           FStar_Parser_AST.attrs = uu____328;_}::uu____329)
              -> d
          | FStar_Parser_AST.Interface
              (uu____336,{ FStar_Parser_AST.d = uu____337;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____339;
                           FStar_Parser_AST.quals = uu____340;
                           FStar_Parser_AST.attrs = uu____341;_}::uu____342,uu____343)
              -> d
          | uu____350 -> FStar_Range.dummyRange  in
        let uu____351 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____351 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____363 =
              let uu____368 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_tcenv env) uu____368  in
            (match uu____363 with
             | (ast_modul1,env1) ->
                 let uu____392 =
                   let uu____397 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_tcenv env1) uu____397  in
                 (match uu____392 with
                  | (modul,env2) ->
                      ((let uu____422 =
                          let uu____423 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____423  in
                        if uu____422
                        then
                          let msg =
                            let uu____425 =
                              let uu____426 =
                                let uu____427 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____427  in
                              FStar_Parser_Dep.module_name_of_file uu____426
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____425
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____431 =
                          let uu____440 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____440
                          then (modul, [], env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul
                           in
                        match uu____431 with
                        | (modul1,uu____459,env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____476 = FStar_List.hd ast_decls  in
                 (match uu____476 with
                  | { FStar_Parser_AST.d = uu____483;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____485;
                      FStar_Parser_AST.quals = uu____486;
                      FStar_Parser_AST.attrs = uu____487;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____497 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____515 =
                            let uu____522 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_tcenv env1) uu____522
                             in
                          match uu____515 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____497 with
                  | (env1,ast_decls_l) ->
                      let uu____576 =
                        let uu____583 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_tcenv env1) uu____583  in
                      (match uu____576 with
                       | (sigelts,env2) ->
                           let uu____619 =
                             let uu____628 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____628
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____619 with
                            | (modul1,uu____647,env3) ->
                                ((FStar_Pervasives_Native.Some modul1), env3)))))
  
let (load_interface_decls :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun interface_file_name  ->
      let r =
        FStar_Parser_ParseIt.parse
          (FStar_Parser_ParseIt.Filename interface_file_name)
         in
      match r with
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Util.Inl (FStar_Parser_AST.Interface
           (l,decls,uu____668)),uu____669)
          ->
          let uu____688 =
            let uu____693 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_tcenv env) uu____693  in
          FStar_Pervasives_Native.snd uu____688
      | FStar_Parser_ParseIt.ASTFragment uu____709 ->
          let uu____720 =
            let uu____725 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____725)  in
          FStar_Errors.raise_err uu____720
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____729 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
  
let (load_module_from_cache :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      (FStar_Syntax_Syntax.modul,FStar_Syntax_Syntax.modul
                                   FStar_Pervasives_Native.option,FStar_Syntax_DsEnv.module_inclusion_info)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  let some_cache_invalid = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let invalidate_cache fn =
    FStar_ST.op_Colon_Equals some_cache_invalid
      (FStar_Pervasives_Native.Some ())
     in
  let load1 env source_file cache_file =
    let uu____834 = FStar_Util.load_value_from_file cache_file  in
    match uu____834 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inl "Corrupt"
    | FStar_Pervasives_Native.Some (vnum,digest,tcmod,tcmod_iface_opt,mii) ->
        if vnum <> cache_version_number
        then FStar_Util.Inl "Stale, because inconsistent cache version"
        else
          (let uu____971 =
             let uu____980 = FStar_TypeChecker_Env.dep_graph env  in
             FStar_Parser_Dep.hash_dependences uu____980 source_file  in
           match uu____971 with
           | FStar_Pervasives_Native.Some digest' ->
               if digest = digest'
               then FStar_Util.Inr (tcmod, tcmod_iface_opt, mii)
               else
                 ((let uu____1036 = FStar_Options.debug_any ()  in
                   if uu____1036
                   then
                     ((let uu____1038 =
                         FStar_Util.string_of_int (FStar_List.length digest')
                          in
                       let uu____1043 = FStar_Parser_Dep.print_digest digest'
                          in
                       let uu____1044 =
                         FStar_Util.string_of_int (FStar_List.length digest)
                          in
                       let uu____1049 = FStar_Parser_Dep.print_digest digest
                          in
                       FStar_Util.print4
                         "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                         uu____1038 uu____1043 uu____1044 uu____1049);
                      if
                        (FStar_List.length digest) =
                          (FStar_List.length digest')
                      then
                        FStar_List.iter2
                          (fun uu____1074  ->
                             fun uu____1075  ->
                               match (uu____1074, uu____1075) with
                               | ((x,y),(x',y')) ->
                                   if (x <> x') || (y <> y')
                                   then
                                     let uu____1104 =
                                       FStar_Parser_Dep.print_digest [(x, y)]
                                        in
                                     let uu____1113 =
                                       FStar_Parser_Dep.print_digest
                                         [(x', y')]
                                        in
                                     FStar_Util.print2
                                       "Differ at: Expected %s\n Got %s\n"
                                       uu____1104 uu____1113
                                   else ()) digest digest'
                      else ())
                   else ());
                  FStar_Util.Inl "Stale")
           | uu____1133 -> FStar_Util.Inl "Unable to compute digest of")
     in
  fun env  ->
    fun fn  ->
      let cache_file = FStar_Parser_Dep.cache_file_name fn  in
      let fail1 tag should_warn cache_file1 =
        invalidate_cache ();
        if should_warn
        then
          (let uu____1181 =
             let uu____1182 =
               FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
                in
             let uu____1183 =
               FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
                in
             FStar_Range.mk_range fn uu____1182 uu____1183  in
           let uu____1184 =
             let uu____1189 =
               FStar_Util.format3
                 "%s cache file %s; will recheck %s and all subsequent files"
                 tag cache_file1 fn
                in
             (FStar_Errors.Warning_CachedFile, uu____1189)  in
           FStar_Errors.log_issue uu____1181 uu____1184)
        else ();
        FStar_Pervasives_Native.None  in
      let uu____1199 = FStar_ST.op_Bang some_cache_invalid  in
      match uu____1199 with
      | FStar_Pervasives_Native.Some uu____1257 ->
          FStar_Pervasives_Native.None
      | uu____1266 ->
          if FStar_Util.file_exists cache_file
          then
            let uu____1279 = load1 env fn cache_file  in
            (match uu____1279 with
             | FStar_Util.Inl msg -> fail1 msg true cache_file
             | FStar_Util.Inr res -> FStar_Pervasives_Native.Some res)
          else
            (let uu____1337 =
               let uu____1340 = FStar_Util.basename cache_file  in
               FStar_Options.find_file uu____1340  in
             match uu____1337 with
             | FStar_Pervasives_Native.None  ->
                 fail1 "Absent" false cache_file
             | FStar_Pervasives_Native.Some alt_cache_file ->
                 let uu____1352 = load1 env fn alt_cache_file  in
                 (match uu____1352 with
                  | FStar_Util.Inl msg -> fail1 msg true alt_cache_file
                  | FStar_Util.Inr res ->
                      ((let uu____1402 = FStar_Options.should_verify_file fn
                           in
                        if uu____1402
                        then FStar_Util.copy_file alt_cache_file cache_file
                        else ());
                       FStar_Pervasives_Native.Some res)))
  
let (store_module_to_cache :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.modul ->
        FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
          FStar_Syntax_DsEnv.module_inclusion_info -> unit)
  =
  fun env  ->
    fun fn  ->
      fun m  ->
        fun modul_iface_opt  ->
          fun mii  ->
            let uu____1441 =
              (FStar_Options.cache_checked_modules ()) &&
                (let uu____1443 = FStar_Options.cache_off ()  in
                 Prims.op_Negation uu____1443)
               in
            if uu____1441
            then
              let cache_file = FStar_Parser_Dep.cache_file_name fn  in
              let digest =
                let uu____1454 = FStar_TypeChecker_Env.dep_graph env  in
                FStar_Parser_Dep.hash_dependences uu____1454 fn  in
              match digest with
              | FStar_Pervasives_Native.Some hashes ->
                  FStar_Util.save_value_to_file cache_file
                    (cache_version_number, hashes, m, modul_iface_opt, mii)
              | uu____1494 ->
                  let uu____1503 =
                    let uu____1504 =
                      FStar_Range.mk_pos (Prims.parse_int "0")
                        (Prims.parse_int "0")
                       in
                    let uu____1505 =
                      FStar_Range.mk_pos (Prims.parse_int "0")
                        (Prims.parse_int "0")
                       in
                    FStar_Range.mk_range fn uu____1504 uu____1505  in
                  let uu____1506 =
                    let uu____1511 =
                      FStar_Util.format1
                        "%s was not written, since some of its dependences were not also checked"
                        cache_file
                       in
                    (FStar_Errors.Warning_FileNotWritten, uu____1511)  in
                  FStar_Errors.log_issue uu____1503 uu____1506
            else ()
  
type delta_env =
  (FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.option
let (apply_delta_env :
  FStar_TypeChecker_Env.env -> delta_env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun f  ->
      match f with
      | FStar_Pervasives_Native.None  -> env
      | FStar_Pervasives_Native.Some f1 -> f1 env
  
let (extend_delta_env :
  delta_env ->
    (FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) ->
      (FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.option)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some g
      | FStar_Pervasives_Native.Some f1 ->
          FStar_Pervasives_Native.Some
            ((fun e  -> let uu____1589 = f1 e  in g uu____1589))
  
let (tc_one_file :
  FStar_TypeChecker_Env.env ->
    delta_env ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((FStar_Syntax_Syntax.modul,Prims.int)
             FStar_Pervasives_Native.tuple2,FStar_TypeChecker_Env.env,
            delta_env) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun delta1  ->
      fun pre_fn  ->
        fun fn  ->
          FStar_Syntax_Syntax.reset_gensym ();
          (let tc_source_file uu____1656 =
             let env1 = apply_delta_env env delta1  in
             let uu____1660 = parse env1 pre_fn fn  in
             match uu____1660 with
             | (fmod,env2) ->
                 let check_mod uu____1698 =
                   let uu____1699 =
                     FStar_Util.record_time
                       (fun uu____1721  ->
                          FStar_TypeChecker_Tc.check_module env2 fmod
                            (FStar_Util.is_some pre_fn))
                      in
                   match uu____1699 with
                   | ((tcmod,tcmod_iface_opt,env3),time) ->
                       ((tcmod, time), tcmod_iface_opt, env3)
                    in
                 let uu____1756 =
                   let uu____1769 =
                     (FStar_Options.should_verify
                        (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                       &&
                       ((FStar_Options.record_hints ()) ||
                          (FStar_Options.use_hints ()))
                      in
                   if uu____1769
                   then
                     let uu____1782 = FStar_Parser_ParseIt.find_file fn  in
                     FStar_SMTEncoding_Solver.with_hints_db uu____1782
                       check_mod
                   else check_mod ()  in
                 (match uu____1756 with
                  | (tcmod,tcmod_iface_opt,env3) ->
                      let mii =
                        FStar_Syntax_DsEnv.inclusion_info
                          env3.FStar_TypeChecker_Env.dsenv
                          (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name
                         in
                      (tcmod, tcmod_iface_opt, mii, env3))
              in
           let uu____1832 =
             let uu____1833 = FStar_Options.cache_off ()  in
             Prims.op_Negation uu____1833  in
           if uu____1832
           then
             let uu____1844 = load_module_from_cache env fn  in
             match uu____1844 with
             | FStar_Pervasives_Native.None  ->
                 let uu____1873 = tc_source_file ()  in
                 (match uu____1873 with
                  | (tcmod,tcmod_iface_opt,mii,env1) ->
                      ((let uu____1915 =
                          (let uu____1918 = FStar_Errors.get_err_count ()  in
                           uu____1918 = (Prims.parse_int "0")) &&
                            ((FStar_Options.lax ()) ||
                               (FStar_Options.should_verify
                                  ((FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name).FStar_Ident.str))
                           in
                        if uu____1915
                        then
                          store_module_to_cache env1 fn
                            (FStar_Pervasives_Native.fst tcmod)
                            tcmod_iface_opt mii
                        else ());
                       (tcmod, env1, FStar_Pervasives_Native.None)))
             | FStar_Pervasives_Native.Some (tcmod,tcmod_iface_opt,mii) ->
                 ((let uu____1943 =
                     FStar_Options.dump_module
                       (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                      in
                   if uu____1943
                   then
                     let uu____1944 =
                       FStar_Syntax_Print.modul_to_string tcmod  in
                     FStar_Util.print1 "Module after type checking:\n%s\n"
                       uu____1944
                   else ());
                  (let tcmod1 =
                     if tcmod.FStar_Syntax_Syntax.is_interface
                     then tcmod
                     else
                       (let use_interface_from_the_cache =
                          ((FStar_Options.use_extracted_interfaces ()) &&
                             (pre_fn = FStar_Pervasives_Native.None))
                            &&
                            (let uu____1952 =
                               (FStar_Options.expose_interfaces ()) &&
                                 (FStar_Options.should_verify
                                    (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                                in
                             Prims.op_Negation uu____1952)
                           in
                        if use_interface_from_the_cache
                        then
                          (if FStar_Option.isNone tcmod_iface_opt
                           then
                             ((let uu____1954 =
                                 let uu____1955 =
                                   FStar_Range.mk_pos (Prims.parse_int "0")
                                     (Prims.parse_int "0")
                                    in
                                 let uu____1956 =
                                   FStar_Range.mk_pos (Prims.parse_int "0")
                                     (Prims.parse_int "0")
                                    in
                                 FStar_Range.mk_range
                                   (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                                   uu____1955 uu____1956
                                  in
                               FStar_Errors.log_issue uu____1954
                                 (FStar_Errors.Warning_MissingInterfaceOrImplementation,
                                   (Prims.strcat
                                      "use_extracted_interfaces option is set but could not find an interface in the cache for: "
                                      (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)));
                              tcmod)
                           else
                             FStar_All.pipe_right tcmod_iface_opt
                               FStar_Util.must)
                        else tcmod)
                      in
                   let delta_env env1 =
                     let uu____1967 =
                       let uu____1972 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1 mii
                           (FStar_TypeChecker_Normalize.erase_universes env1)
                          in
                       FStar_All.pipe_left (with_tcenv env1) uu____1972  in
                     match uu____1967 with
                     | (uu____1988,env2) ->
                         FStar_TypeChecker_Tc.load_checked_module env2 tcmod1
                      in
                   ((tcmod1, (Prims.parse_int "0")), env,
                     (extend_delta_env delta1 delta_env))))
           else
             (let uu____1998 = tc_source_file ()  in
              match uu____1998 with
              | (tcmod,tcmod_iface_opt,uu____2025,env1) ->
                  let tcmod1 =
                    if FStar_Util.is_some tcmod_iface_opt
                    then
                      let uu____2048 =
                        FStar_All.pipe_right tcmod_iface_opt FStar_Util.must
                         in
                      (uu____2048, (FStar_Pervasives_Native.snd tcmod))
                    else tcmod  in
                  (tcmod1, env1, FStar_Pervasives_Native.None)))
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____2072 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____2072 ["fsti"; "fsi"]))
        &&
        (let uu____2074 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____2074 ["fst"; "fs"])
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      delta_env ->
        (Prims.string Prims.list,(FStar_Syntax_Syntax.modul,Prims.int)
                                   FStar_Pervasives_Native.tuple2 Prims.list,
          FStar_TypeChecker_Env.env,delta_env) FStar_Pervasives_Native.tuple4)
  =
  fun remaining  ->
    fun env  ->
      fun delta_env  ->
        let uu____2112 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____2154 =
                tc_one_file env delta_env (FStar_Pervasives_Native.Some intf)
                  impl
                 in
              (match uu____2154 with
               | (m,env1,delta_env1) -> (remaining1, ([m], env1, delta_env1)))
          | intf_or_impl::remaining1 ->
              let uu____2230 =
                tc_one_file env delta_env FStar_Pervasives_Native.None
                  intf_or_impl
                 in
              (match uu____2230 with
               | (m,env1,delta_env1) -> (remaining1, ([m], env1, delta_env1)))
          | [] -> ([], ([], env, delta_env))  in
        match uu____2112 with
        | (remaining1,(nmods,env1,delta_env1)) ->
            (remaining1, nmods, env1, delta_env1)
  
let rec (tc_fold_interleave :
  ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
     Prims.list,FStar_TypeChecker_Env.env,delta_env)
    FStar_Pervasives_Native.tuple3 ->
    Prims.string Prims.list ->
      ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_TypeChecker_Env.env,delta_env)
        FStar_Pervasives_Native.tuple3)
  =
  fun acc  ->
    fun remaining  ->
      match remaining with
      | [] -> acc
      | uu____2448 ->
          let uu____2451 = acc  in
          (match uu____2451 with
           | (mods,env,delta_env) ->
               let uu____2491 =
                 tc_one_file_from_remaining remaining env delta_env  in
               (match uu____2491 with
                | (remaining1,nmods,env1,delta_env1) ->
                    tc_fold_interleave
                      ((FStar_List.append mods nmods), env1, delta_env1)
                      remaining1))
  
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_TypeChecker_Env.env,(FStar_TypeChecker_Env.env ->
                                                 FStar_TypeChecker_Env.env)
                                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun filenames  ->
    fun dep_graph1  ->
      (let uu____2586 = FStar_Options.debug_any ()  in
       if uu____2586
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____2589 =
             let uu____2590 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____2590  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____2589))
       else ());
      (let env = init_env dep_graph1  in
       let uu____2599 =
         tc_fold_interleave ([], env, FStar_Pervasives_Native.None) filenames
          in
       match uu____2599 with
       | (all_mods,env1,delta1) ->
           let solver_refresh env2 =
             (let uu____2664 =
                (FStar_Options.interactive ()) &&
                  (let uu____2666 = FStar_Errors.get_err_count ()  in
                   uu____2666 = (Prims.parse_int "0"))
                 in
              if uu____2664
              then
                (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ()
              else
                (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                  ());
             env2  in
           (all_mods, env1, (extend_delta_env delta1 solver_refresh)))
  