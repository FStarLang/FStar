open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "2") 
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
            (let uu___53_55 = env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___53_55.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___53_55.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___53_55.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___53_55.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___53_55.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___53_55.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___53_55.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___53_55.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___53_55.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___53_55.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___53_55.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___53_55.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___53_55.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___53_55.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___53_55.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___53_55.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___53_55.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___53_55.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___53_55.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___53_55.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___53_55.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___53_55.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.tc_term =
                 (uu___53_55.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___53_55.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___53_55.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___53_55.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___53_55.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___53_55.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___53_55.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___53_55.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___53_55.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___53_55.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___53_55.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___53_55.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___53_55.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.dep_graph =
                 (uu___53_55.FStar_TypeChecker_Env.dep_graph)
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
        (let uu___54_250 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___54_250.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___54_250.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___54_250.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.encode_modul =
             (uu___54_250.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___54_250.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___54_250.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___54_250.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___54_250.FStar_TypeChecker_Env.refresh)
         })
       in
    let env =
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid
       in
    let env1 =
      let uu___55_253 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___55_253.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___55_253.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___55_253.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___55_253.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___55_253.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___55_253.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___55_253.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___55_253.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___55_253.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___55_253.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___55_253.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___55_253.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___55_253.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___55_253.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___55_253.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___55_253.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___55_253.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___55_253.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___55_253.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___55_253.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___55_253.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___55_253.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___55_253.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___55_253.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___55_253.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___55_253.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___55_253.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___55_253.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___55_253.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.proof_ns =
          (uu___55_253.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          FStar_Tactics_Interpreter.synthesize;
        FStar_TypeChecker_Env.splice =
          (uu___55_253.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___55_253.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___55_253.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___55_253.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___55_253.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___55_253.FStar_TypeChecker_Env.dep_graph)
      }  in
    let env2 =
      let uu___56_255 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___56_255.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___56_255.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___56_255.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___56_255.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___56_255.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___56_255.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___56_255.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___56_255.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___56_255.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___56_255.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___56_255.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___56_255.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___56_255.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___56_255.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___56_255.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___56_255.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___56_255.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___56_255.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___56_255.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___56_255.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___56_255.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___56_255.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___56_255.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___56_255.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___56_255.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___56_255.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___56_255.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___56_255.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___56_255.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.proof_ns =
          (uu___56_255.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___56_255.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Interpreter.splice;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___56_255.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___56_255.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___56_255.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___56_255.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___56_255.FStar_TypeChecker_Env.dep_graph)
      }  in
    let env3 =
      let uu___57_257 = env2  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___57_257.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___57_257.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___57_257.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___57_257.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___57_257.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___57_257.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___57_257.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___57_257.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___57_257.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___57_257.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___57_257.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___57_257.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___57_257.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___57_257.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___57_257.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___57_257.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___57_257.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___57_257.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___57_257.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___57_257.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___57_257.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___57_257.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___57_257.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___57_257.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___57_257.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___57_257.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___57_257.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___57_257.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___57_257.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.proof_ns =
          (uu___57_257.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___57_257.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___57_257.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___57_257.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___57_257.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___57_257.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___57_257.FStar_TypeChecker_Env.dep_graph)
      }  in
    (env3.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env3; env3
  
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
          let uu____290 =
            let uu____291 =
              let uu____292 = FStar_Options.file_list ()  in
              FStar_List.hd uu____292  in
            FStar_Parser_Dep.lowercase_module_name uu____291  in
          let uu____295 =
            let uu____296 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____296  in
          uu____290 = uu____295  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____303,{ FStar_Parser_AST.d = uu____304;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____306;
                           FStar_Parser_AST.quals = uu____307;
                           FStar_Parser_AST.attrs = uu____308;_}::uu____309)
              -> d
          | FStar_Parser_AST.Interface
              (uu____316,{ FStar_Parser_AST.d = uu____317;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____319;
                           FStar_Parser_AST.quals = uu____320;
                           FStar_Parser_AST.attrs = uu____321;_}::uu____322,uu____323)
              -> d
          | uu____330 -> FStar_Range.dummyRange  in
        let uu____331 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____331 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____343 =
              let uu____348 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_tcenv env) uu____348  in
            (match uu____343 with
             | (ast_modul1,env1) ->
                 let uu____372 =
                   let uu____377 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_tcenv env1) uu____377  in
                 (match uu____372 with
                  | (modul,env2) ->
                      ((let uu____402 =
                          let uu____403 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____403  in
                        if uu____402
                        then
                          let msg =
                            let uu____405 =
                              let uu____406 =
                                let uu____407 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____407  in
                              FStar_Parser_Dep.module_name_of_file uu____406
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____405
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____411 =
                          let uu____420 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____420
                          then (modul, [], env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul
                           in
                        match uu____411 with
                        | (modul1,uu____439,env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____456 = FStar_List.hd ast_decls  in
                 (match uu____456 with
                  | { FStar_Parser_AST.d = uu____463;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____465;
                      FStar_Parser_AST.quals = uu____466;
                      FStar_Parser_AST.attrs = uu____467;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____477 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____495 =
                            let uu____502 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_tcenv env1) uu____502
                             in
                          match uu____495 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____477 with
                  | (env1,ast_decls_l) ->
                      let uu____556 =
                        let uu____561 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_tcenv env1) uu____561  in
                      (match uu____556 with
                       | (sigelts,env2) ->
                           let uu____585 =
                             let uu____594 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____594
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____585 with
                            | (modul1,uu____613,env3) ->
                                ((FStar_Pervasives_Native.Some modul1), env3)))))
  
let (load_interface_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Parser_ParseIt.filename -> FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun interface_file_name  ->
      let r =
        FStar_Parser_ParseIt.parse
          (FStar_Parser_ParseIt.Filename interface_file_name)
         in
      match r with
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Util.Inl (FStar_Parser_AST.Interface
           (l,decls,uu____634)),uu____635)
          ->
          let uu____660 =
            let uu____665 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_tcenv env) uu____665  in
          FStar_Pervasives_Native.snd uu____660
      | FStar_Parser_ParseIt.ASTFragment uu____681 ->
          let uu____692 =
            let uu____697 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____697)  in
          FStar_Errors.raise_err uu____692
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____701 ->
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
    let uu____810 = FStar_Util.load_value_from_file cache_file  in
    match uu____810 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inl "Corrupt"
    | FStar_Pervasives_Native.Some (vnum,digest,tcmod,tcmod_iface_opt,mii) ->
        if vnum <> cache_version_number
        then FStar_Util.Inl "Stale, because inconsistent cache version"
        else
          (let uu____947 =
             FStar_Parser_Dep.hash_dependences
               env.FStar_TypeChecker_Env.dep_graph source_file
              in
           match uu____947 with
           | FStar_Pervasives_Native.Some digest' ->
               if digest = digest'
               then FStar_Util.Inr (tcmod, tcmod_iface_opt, mii)
               else
                 ((let uu____1011 = FStar_Options.debug_any ()  in
                   if uu____1011
                   then
                     ((let uu____1013 =
                         FStar_Util.string_of_int (FStar_List.length digest')
                          in
                       let uu____1018 = FStar_Parser_Dep.print_digest digest'
                          in
                       let uu____1019 =
                         FStar_Util.string_of_int (FStar_List.length digest)
                          in
                       let uu____1024 = FStar_Parser_Dep.print_digest digest
                          in
                       FStar_Util.print4
                         "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                         uu____1013 uu____1018 uu____1019 uu____1024);
                      if
                        (FStar_List.length digest) =
                          (FStar_List.length digest')
                      then
                        FStar_List.iter2
                          (fun uu____1049  ->
                             fun uu____1050  ->
                               match (uu____1049, uu____1050) with
                               | ((x,y),(x',y')) ->
                                   if (x <> x') || (y <> y')
                                   then
                                     let uu____1079 =
                                       FStar_Parser_Dep.print_digest [(x, y)]
                                        in
                                     let uu____1088 =
                                       FStar_Parser_Dep.print_digest
                                         [(x', y')]
                                        in
                                     FStar_Util.print2
                                       "Differ at: Expected %s\n Got %s\n"
                                       uu____1079 uu____1088
                                   else ()) digest digest'
                      else ())
                   else ());
                  FStar_Util.Inl "Stale")
           | uu____1108 -> FStar_Util.Inl "Stale")
     in
  fun env  ->
    fun fn  ->
      let cache_file = FStar_Parser_Dep.cache_file_name fn  in
      let fail1 tag =
        invalidate_cache ();
        (let uu____1146 =
           let uu____1147 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
              in
           let uu____1148 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
              in
           FStar_Range.mk_range fn uu____1147 uu____1148  in
         let uu____1149 =
           let uu____1154 =
             FStar_Util.format3
               "%s cache file %s; will recheck %s and all subsequent files"
               tag cache_file fn
              in
           (FStar_Errors.Warning_CachedFile, uu____1154)  in
         FStar_Errors.log_issue uu____1146 uu____1149);
        FStar_Pervasives_Native.None  in
      let uu____1163 = FStar_ST.op_Bang some_cache_invalid  in
      match uu____1163 with
      | FStar_Pervasives_Native.Some uu____1225 ->
          FStar_Pervasives_Native.None
      | uu____1234 ->
          if FStar_Util.file_exists cache_file
          then
            let uu____1247 = load1 env fn cache_file  in
            (match uu____1247 with
             | FStar_Util.Inl msg -> fail1 msg
             | FStar_Util.Inr res -> FStar_Pervasives_Native.Some res)
          else
            (let uu____1305 =
               let uu____1308 = FStar_Util.basename cache_file  in
               FStar_Options.find_file uu____1308  in
             match uu____1305 with
             | FStar_Pervasives_Native.None  ->
                 (invalidate_cache (); FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some alt_cache_file ->
                 let uu____1329 = load1 env fn alt_cache_file  in
                 (match uu____1329 with
                  | FStar_Util.Inl msg -> fail1 msg
                  | FStar_Util.Inr res ->
                      ((let uu____1379 = FStar_Options.should_verify_file fn
                           in
                        if uu____1379
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
            let cache_file = FStar_Parser_Dep.cache_file_name fn  in
            let digest =
              FStar_Parser_Dep.hash_dependences
                env.FStar_TypeChecker_Env.dep_graph fn
               in
            match digest with
            | FStar_Pervasives_Native.Some hashes ->
                FStar_Util.save_value_to_file cache_file
                  (cache_version_number, hashes, m, modul_iface_opt, mii)
            | uu____1467 ->
                let uu____1476 =
                  let uu____1477 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  let uu____1478 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  FStar_Range.mk_range fn uu____1477 uu____1478  in
                let uu____1479 =
                  let uu____1484 =
                    FStar_Util.format1
                      "%s was not written, since some of its dependences were not also checked"
                      cache_file
                     in
                  (FStar_Errors.Warning_FileNotWritten, uu____1484)  in
                FStar_Errors.log_issue uu____1476 uu____1479
  
type delta_env =
  (FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.option[@@deriving show]
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
            ((fun e  -> let uu____1561 = f1 e  in g uu____1561))
  
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
          (let tc_source_file uu____1628 =
             let env1 = apply_delta_env env delta1  in
             let uu____1632 = parse env1 pre_fn fn  in
             match uu____1632 with
             | (fmod,env2) ->
                 let check_mod uu____1670 =
                   let uu____1671 =
                     FStar_Util.record_time
                       (fun uu____1693  ->
                          FStar_TypeChecker_Tc.check_module env2 fmod
                            (FStar_Util.is_some pre_fn))
                      in
                   match uu____1671 with
                   | ((tcmod,tcmod_iface_opt,env3),time) ->
                       ((tcmod, time), tcmod_iface_opt, env3)
                    in
                 let uu____1728 =
                   let uu____1741 =
                     (FStar_Options.should_verify
                        (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                       &&
                       ((FStar_Options.record_hints ()) ||
                          (FStar_Options.use_hints ()))
                      in
                   if uu____1741
                   then
                     let uu____1754 = FStar_Parser_ParseIt.find_file fn  in
                     FStar_SMTEncoding_Solver.with_hints_db uu____1754
                       check_mod
                   else check_mod ()  in
                 (match uu____1728 with
                  | (tcmod,tcmod_iface_opt,env3) ->
                      let mii =
                        FStar_Syntax_DsEnv.inclusion_info
                          env3.FStar_TypeChecker_Env.dsenv
                          (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name
                         in
                      (tcmod, tcmod_iface_opt, mii, env3))
              in
           let uu____1804 = load_module_from_cache env fn  in
           match uu____1804 with
           | FStar_Pervasives_Native.None  ->
               let uu____1833 = tc_source_file ()  in
               (match uu____1833 with
                | (tcmod,tcmod_iface_opt,mii,env1) ->
                    ((let uu____1875 =
                        ((let uu____1878 = FStar_Errors.get_err_count ()  in
                          uu____1878 = (Prims.parse_int "0")) &&
                           (FStar_Options.cache_checked_modules ()))
                          &&
                          ((FStar_Options.lax ()) ||
                             (FStar_Options.should_verify
                                ((FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name).FStar_Ident.str))
                         in
                      if uu____1875
                      then
                        store_module_to_cache env1 fn
                          (FStar_Pervasives_Native.fst tcmod) tcmod_iface_opt
                          mii
                      else ());
                     (tcmod, env1, FStar_Pervasives_Native.None)))
           | FStar_Pervasives_Native.Some (tcmod,tcmod_iface_opt,mii) ->
               let tcmod1 =
                 if tcmod.FStar_Syntax_Syntax.is_interface
                 then tcmod
                 else
                   (let use_interface_from_the_cache =
                      (FStar_Options.use_extracted_interfaces ()) &&
                        (let uu____1911 =
                           (FStar_Options.expose_interfaces ()) &&
                             (FStar_Options.should_verify
                                (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                            in
                         Prims.op_Negation uu____1911)
                       in
                    if use_interface_from_the_cache
                    then
                      (if tcmod_iface_opt = FStar_Pervasives_Native.None
                       then
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_ModuleNotFound,
                             (Prims.strcat
                                "use_extracted_interfaces option is set but could not find it in the cache for: "
                                (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str))
                           FStar_Range.dummyRange
                       else
                         FStar_All.pipe_right tcmod_iface_opt FStar_Util.must)
                    else tcmod)
                  in
               let delta_env env1 =
                 let uu____1924 =
                   let uu____1929 =
                     FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1 mii
                       (FStar_TypeChecker_Normalize.erase_universes env1)
                      in
                   FStar_All.pipe_left (with_tcenv env1) uu____1929  in
                 match uu____1924 with
                 | (uu____1945,env2) ->
                     FStar_TypeChecker_Tc.load_checked_module env2 tcmod1
                  in
               ((tcmod1, (Prims.parse_int "0")), env,
                 (extend_delta_env delta1 delta_env)))
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____1972 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____1972 ["fsti"; "fsi"]))
        &&
        (let uu____1974 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____1974 ["fst"; "fs"])
  
let (pop_context : FStar_TypeChecker_Env.env -> Prims.string -> unit) =
  fun env  ->
    fun msg  ->
      let uu____1985 = FStar_TypeChecker_Tc.pop_context env msg  in
      FStar_All.pipe_right uu____1985 (fun a239  -> ())
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  -> fun msg  -> FStar_TypeChecker_Tc.push_context env msg 
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
        let uu____2033 =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu____2075 =
                tc_one_file env delta_env (FStar_Pervasives_Native.Some intf)
                  impl
                 in
              (match uu____2075 with
               | (m,env1,delta_env1) -> (remaining1, ([m], env1, delta_env1)))
          | intf_or_impl::remaining1 ->
              let uu____2151 =
                tc_one_file env delta_env FStar_Pervasives_Native.None
                  intf_or_impl
                 in
              (match uu____2151 with
               | (m,env1,delta_env1) -> (remaining1, ([m], env1, delta_env1)))
          | [] -> ([], ([], env, delta_env))  in
        match uu____2033 with
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
      | uu____2369 ->
          let uu____2372 = acc  in
          (match uu____2372 with
           | (mods,env,delta_env) ->
               let uu____2412 =
                 tc_one_file_from_remaining remaining env delta_env  in
               (match uu____2412 with
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
      (let uu____2507 = FStar_Options.debug_any ()  in
       if uu____2507
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____2510 =
             let uu____2511 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____2511  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____2510))
       else ());
      (let env = init_env dep_graph1  in
       let uu____2520 =
         tc_fold_interleave ([], env, FStar_Pervasives_Native.None) filenames
          in
       match uu____2520 with
       | (all_mods,env1,delta1) ->
           let solver_refresh env2 =
             (let uu____2590 =
                (FStar_Options.interactive ()) &&
                  (let uu____2592 = FStar_Errors.get_err_count ()  in
                   uu____2592 = (Prims.parse_int "0"))
                 in
              if uu____2590
              then
                (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ()
              else
                (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                  ());
             env2  in
           (all_mods, env1, (extend_delta_env delta1 solver_refresh)))
  