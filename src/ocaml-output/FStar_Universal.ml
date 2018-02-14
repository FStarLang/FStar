open Prims
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul ->
    (Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2)
  =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
  
let (user_tactics_modules : Prims.string Prims.list FStar_ST.ref) =
  FStar_TypeChecker_Tc.user_tactics_modules 
let with_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_ToSyntax_Env.withenv ->
        ('a,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____73 = f env.FStar_TypeChecker_Env.dsenv  in
      match uu____73 with
      | (a,dsenv) ->
          (a,
            (let uu___50_87 = env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___50_87.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___50_87.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___50_87.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___50_87.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___50_87.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___50_87.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___50_87.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___50_87.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___50_87.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___50_87.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___50_87.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___50_87.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___50_87.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___50_87.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___50_87.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___50_87.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___50_87.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___50_87.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___50_87.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___50_87.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___50_87.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___50_87.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.tc_term =
                 (uu___50_87.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___50_87.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___50_87.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___50_87.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___50_87.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___50_87.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___50_87.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___50_87.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___50_87.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___50_87.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___50_87.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv;
               FStar_TypeChecker_Env.dep_graph =
                 (uu___50_87.FStar_TypeChecker_Env.dep_graph)
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
        let uu____109 = FStar_Parser_Driver.parse_file fn  in
        match uu____109 with
        | (ast,uu____125) ->
            let uu____138 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____148 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____148 with
                   | (pre_ast,uu____164) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____183),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____194 =
                              let uu____199 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              FStar_All.pipe_left (with_tcenv env) uu____199
                               in
                            (match uu____194 with
                             | (uu____216,env1) ->
                                 let uu____218 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 FStar_All.pipe_left (with_tcenv env1)
                                   uu____218)
                        | uu____231 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____138 with
             | (ast1,env1) ->
                 let uu____246 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 FStar_All.pipe_left (with_tcenv env1) uu____246)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____263 = FStar_Options.lax ()  in
      if uu____263
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___51_265 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___51_265.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___51_265.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___51_265.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.encode_modul =
             (uu___51_265.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___51_265.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___51_265.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___51_265.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___51_265.FStar_TypeChecker_Env.refresh)
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
      let uu___52_268 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___52_268.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___52_268.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___52_268.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___52_268.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___52_268.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___52_268.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___52_268.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___52_268.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___52_268.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___52_268.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___52_268.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___52_268.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___52_268.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___52_268.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___52_268.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___52_268.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___52_268.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___52_268.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___52_268.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___52_268.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___52_268.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___52_268.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___52_268.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___52_268.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___52_268.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___52_268.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___52_268.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___52_268.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___52_268.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___52_268.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___52_268.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___52_268.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___52_268.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___52_268.FStar_TypeChecker_Env.dep_graph)
      }  in
    let env2 =
      let uu___53_270 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___53_270.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___53_270.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___53_270.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___53_270.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___53_270.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___53_270.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___53_270.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___53_270.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___53_270.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___53_270.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___53_270.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___53_270.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___53_270.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___53_270.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___53_270.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___53_270.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___53_270.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___53_270.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___53_270.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___53_270.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___53_270.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___53_270.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___53_270.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___53_270.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___53_270.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___53_270.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___53_270.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___53_270.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___53_270.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___53_270.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___53_270.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___53_270.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___53_270.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___53_270.FStar_TypeChecker_Env.dep_graph)
      }  in
    (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env2; env2
  
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
          let uu____295 =
            let uu____296 =
              let uu____297 = FStar_Options.file_list ()  in
              FStar_List.hd uu____297  in
            FStar_Parser_Dep.lowercase_module_name uu____296  in
          let uu____300 =
            let uu____301 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____301  in
          uu____295 = uu____300  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____306,{ FStar_Parser_AST.d = uu____307;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____309;
                           FStar_Parser_AST.quals = uu____310;
                           FStar_Parser_AST.attrs = uu____311;_}::uu____312)
              -> d
          | FStar_Parser_AST.Interface
              (uu____319,{ FStar_Parser_AST.d = uu____320;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____322;
                           FStar_Parser_AST.quals = uu____323;
                           FStar_Parser_AST.attrs = uu____324;_}::uu____325,uu____326)
              -> d
          | uu____333 -> FStar_Range.dummyRange  in
        let uu____334 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____334 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____346 =
              let uu____351 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_tcenv env) uu____351  in
            (match uu____346 with
             | (ast_modul1,env1) ->
                 let uu____372 =
                   let uu____377 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_tcenv env1) uu____377  in
                 (match uu____372 with
                  | (modul,env2) ->
                      ((let uu____399 =
                          let uu____400 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____400  in
                        if uu____399
                        then
                          let msg =
                            let uu____402 =
                              let uu____403 =
                                let uu____404 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____404  in
                              FStar_Parser_Dep.module_name_of_file uu____403
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____402
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____408 =
                          let uu____413 =
                            FStar_ToSyntax_Env.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____413
                          then (modul, env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul
                              false
                           in
                        match uu____408 with
                        | (modul1,env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____438 = FStar_List.hd ast_decls  in
                 (match uu____438 with
                  | { FStar_Parser_AST.d = uu____445;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____447;
                      FStar_Parser_AST.quals = uu____448;
                      FStar_Parser_AST.attrs = uu____449;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____459 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____477 =
                            let uu____484 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_tcenv env1) uu____484
                             in
                          match uu____477 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____459 with
                  | (env1,ast_decls_l) ->
                      let uu____535 =
                        let uu____540 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_tcenv env1) uu____540  in
                      (match uu____535 with
                       | (sigelts,env2) ->
                           let uu____561 =
                             let uu____566 =
                               FStar_ToSyntax_Env.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____566
                             then (modul, env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____561 with
                            | (modul1,env3) ->
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
           (l,decls,uu____591)),uu____592)
          ->
          let uu____617 =
            let uu____622 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_tcenv env) uu____622  in
          FStar_Pervasives_Native.snd uu____617
      | FStar_Parser_ParseIt.ASTFragment uu____635 ->
          let uu____646 =
            let uu____651 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____651)  in
          FStar_Errors.raise_err uu____646
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____655 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
  
let (load_module_from_cache :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      (FStar_Syntax_Syntax.modul,FStar_ToSyntax_Env.module_inclusion_info)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fn  ->
      let cache_file =
        let uu____675 =
          FStar_Parser_Dep.all_cmd_line_files
            env.FStar_TypeChecker_Env.dep_graph
           in
        FStar_Parser_Dep.cache_file_name uu____675 fn  in
      FStar_Util.print1 "Loading module from cache: %s\n\n" cache_file;
      (let fail1 tag =
         (let uu____690 =
            let uu____691 =
              FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
               in
            let uu____692 =
              FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
               in
            FStar_Range.mk_range fn uu____691 uu____692  in
          let uu____693 =
            let uu____698 =
              FStar_Util.format3 "%s cache file %s; will recheck %s" tag
                cache_file fn
               in
            (FStar_Errors.Warning_CachedFile, uu____698)  in
          FStar_Errors.log_issue uu____690 uu____693);
         FStar_Pervasives_Native.None  in
       if FStar_Util.file_exists cache_file
       then
         let uu____709 = FStar_Util.load_value_from_file cache_file  in
         match uu____709 with
         | FStar_Pervasives_Native.None  -> fail1 "Corrupt"
         | FStar_Pervasives_Native.Some (digest,tcmod,mii) ->
             let uu____781 =
               FStar_Parser_Dep.hash_dependences
                 env.FStar_TypeChecker_Env.dep_graph fn
                in
             (match uu____781 with
              | FStar_Pervasives_Native.Some digest' ->
                  if digest = digest'
                  then
                    ((let uu____822 =
                        FStar_Options.dump_module
                          (tcmod.FStar_Syntax_Syntax.name).FStar_Ident.str
                         in
                      if uu____822
                      then
                        let uu____823 =
                          FStar_Syntax_Print.modul_to_string tcmod  in
                        FStar_Util.print1 "\n\nLoaded from cache: %s\n\n"
                          uu____823
                      else ());
                     FStar_Pervasives_Native.Some (tcmod, mii))
                  else
                    ((let uu____831 = FStar_Options.debug_any ()  in
                      if uu____831
                      then
                        ((let uu____833 =
                            FStar_Util.string_of_int
                              (FStar_List.length digest')
                             in
                          let uu____838 =
                            FStar_Parser_Dep.print_digest digest'  in
                          let uu____839 =
                            FStar_Util.string_of_int
                              (FStar_List.length digest)
                             in
                          let uu____844 =
                            FStar_Parser_Dep.print_digest digest  in
                          FStar_Util.print4
                            "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                            uu____833 uu____838 uu____839 uu____844);
                         if
                           (FStar_List.length digest) =
                             (FStar_List.length digest')
                         then
                           FStar_List.iter2
                             (fun uu____869  ->
                                fun uu____870  ->
                                  match (uu____869, uu____870) with
                                  | ((x,y),(x',y')) ->
                                      if (x <> x) || (y <> y')
                                      then
                                        let uu____899 =
                                          FStar_Parser_Dep.print_digest
                                            [(x, y)]
                                           in
                                        let uu____908 =
                                          FStar_Parser_Dep.print_digest
                                            [(x', y')]
                                           in
                                        FStar_Util.print2
                                          "Differ at: Expected %s\n Got %s\n"
                                          uu____899 uu____908
                                      else ()) digest digest'
                         else ())
                      else ());
                     fail1 "Stale")
              | uu____920 -> fail1 "Stale")
       else fail1 "Absent")
  
let (store_module_to_cache :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.modul ->
        FStar_ToSyntax_Env.module_inclusion_info -> Prims.unit)
  =
  fun env  ->
    fun fn  ->
      fun modul  ->
        fun mii  ->
          let cache_file =
            let uu____943 =
              FStar_Parser_Dep.all_cmd_line_files
                env.FStar_TypeChecker_Env.dep_graph
               in
            FStar_Parser_Dep.cache_file_name uu____943 fn  in
          FStar_Util.print1 "Storing module to cache: %s\n\n" cache_file;
          (let uu____948 =
             FStar_Options.dump_module
               (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           if uu____948
           then
             let uu____949 = FStar_Syntax_Print.modul_to_string modul  in
             FStar_Util.print1 "\n\nStoring to cache: %s\n\n" uu____949
           else ());
          (let digest =
             FStar_Parser_Dep.hash_dependences
               env.FStar_TypeChecker_Env.dep_graph fn
              in
           match digest with
           | FStar_Pervasives_Native.Some hashes ->
               FStar_Util.save_value_to_file cache_file (hashes, modul, mii)
           | uu____991 ->
               let uu____1000 =
                 let uu____1001 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 let uu____1002 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 FStar_Range.mk_range fn uu____1001 uu____1002  in
               let uu____1003 =
                 let uu____1008 =
                   FStar_Util.format1
                     "%s was not written, since some of its dependences were not also checked"
                     cache_file
                    in
                 (FStar_Errors.Warning_FileNotWritten, uu____1008)  in
               FStar_Errors.log_issue uu____1000 uu____1003)
  
let (tc_one_file :
  FStar_TypeChecker_Env.env ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        FStar_Syntax_Syntax.reset_gensym ();
        (let tc_source_file uu____1052 =
           let uu____1053 = parse env pre_fn fn  in
           match uu____1053 with
           | (fmod,env1) ->
               let check_mod fmod1 uu____1084 =
                 let uu____1085 =
                   FStar_Util.record_time
                     (fun uu____1099  ->
                        FStar_TypeChecker_Tc.check_module env1 fmod1)
                    in
                 match uu____1085 with
                 | ((tcmod,env2),time) -> ((tcmod, time), env2)  in
               let uu____1119 =
                 let uu____1128 =
                   let uu____1135 =
                     let uu____1136 =
                       FStar_Parser_Dep.all_cmd_line_files
                         env1.FStar_TypeChecker_Env.dep_graph
                        in
                     FStar_Parser_Dep.check_or_use_extracted_interface
                       uu____1136 fn
                      in
                   if uu____1135
                   then
                     (FStar_Util.print1
                        "Extracting interface for: %s, will be using it for type checking/caching\n\n"
                        (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str;
                      (let uu____1146 =
                         FStar_TypeChecker_Tc.extract_interface env1 fmod  in
                       (true, uu____1146,
                         (let uu___54_1148 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___54_1148.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___54_1148.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___54_1148.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___54_1148.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___54_1148.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___54_1148.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___54_1148.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___54_1148.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___54_1148.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___54_1148.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___54_1148.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___54_1148.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___54_1148.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___54_1148.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___54_1148.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___54_1148.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface = true;
                            FStar_TypeChecker_Env.admit =
                              (uu___54_1148.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___54_1148.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___54_1148.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.failhard =
                              (uu___54_1148.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___54_1148.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___54_1148.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___54_1148.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___54_1148.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___54_1148.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___54_1148.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qname_and_index =
                              (uu___54_1148.FStar_TypeChecker_Env.qname_and_index);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___54_1148.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth =
                              (uu___54_1148.FStar_TypeChecker_Env.synth);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___54_1148.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___54_1148.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___54_1148.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___54_1148.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.dep_graph =
                              (uu___54_1148.FStar_TypeChecker_Env.dep_graph)
                          }))))
                   else (false, fmod, env1)  in
                 match uu____1128 with
                 | (checking_or_using_extracted_interface,fmod1,env2) ->
                     let uu____1161 =
                       (FStar_Options.should_verify
                          (fmod1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                         &&
                         ((FStar_Options.record_hints ()) ||
                            (FStar_Options.use_hints ()))
                        in
                     if uu____1161
                     then
                       let uu____1170 = FStar_Parser_ParseIt.find_file fn  in
                       FStar_SMTEncoding_Solver.with_hints_db uu____1170
                         checking_or_using_extracted_interface
                         (check_mod fmod1)
                     else check_mod fmod1 ()
                  in
               (match uu____1119 with
                | (tcmod,env2) ->
                    let mii =
                      FStar_ToSyntax_Env.inclusion_info
                        env2.FStar_TypeChecker_Env.dsenv
                        (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name
                       in
                    (tcmod, mii, env2))
            in
         let uu____1205 = FStar_Options.cache_checked_modules ()  in
         if uu____1205
         then
           let uu____1214 = load_module_from_cache env fn  in
           match uu____1214 with
           | FStar_Pervasives_Native.None  ->
               let uu____1233 = tc_source_file ()  in
               (match uu____1233 with
                | (tcmod,mii,env1) ->
                    ((let uu____1264 =
                        (let uu____1267 = FStar_Errors.get_err_count ()  in
                         uu____1267 = (Prims.parse_int "0")) &&
                          ((FStar_Options.lax ()) ||
                             (FStar_Options.should_verify
                                ((FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name).FStar_Ident.str))
                         in
                      if uu____1264
                      then
                        store_module_to_cache env1 fn
                          (FStar_Pervasives_Native.fst tcmod) mii
                      else ());
                     (tcmod, env1)))
           | FStar_Pervasives_Native.Some (tcmod,mii) ->
               let uu____1279 =
                 let uu____1284 =
                   FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii
                     (FStar_TypeChecker_Normalize.erase_universes env)
                    in
                 FStar_All.pipe_left (with_tcenv env) uu____1284  in
               (match uu____1279 with
                | (uu____1305,env1) ->
                    let env2 =
                      FStar_TypeChecker_Tc.load_checked_module env1 tcmod  in
                    ((tcmod, (Prims.parse_int "0")), env2))
         else
           (let uu____1313 = tc_source_file ()  in
            match uu____1313 with | (tcmod,uu____1333,env1) -> (tcmod, env1)))
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____1356 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____1356 ["fsti"; "fsi"]))
        &&
        (let uu____1358 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____1358 ["fst"; "fs"])
  
let (pop_context : FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit) =
  fun env  ->
    fun msg  ->
      (let uu____1366 = FStar_ToSyntax_Env.pop ()  in
       FStar_All.pipe_right uu____1366 FStar_Pervasives.ignore);
      (let uu____1368 = FStar_TypeChecker_Env.pop env msg  in
       FStar_All.pipe_right uu____1368 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv  in
      let env1 = FStar_TypeChecker_Env.push env msg  in
      let uu___55_1377 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___55_1377.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___55_1377.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___55_1377.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___55_1377.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___55_1377.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___55_1377.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___55_1377.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___55_1377.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___55_1377.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___55_1377.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___55_1377.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___55_1377.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___55_1377.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___55_1377.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___55_1377.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___55_1377.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___55_1377.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___55_1377.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___55_1377.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___55_1377.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___55_1377.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___55_1377.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___55_1377.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___55_1377.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___55_1377.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___55_1377.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___55_1377.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___55_1377.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___55_1377.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___55_1377.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___55_1377.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___55_1377.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___55_1377.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv;
        FStar_TypeChecker_Env.dep_graph =
          (uu___55_1377.FStar_TypeChecker_Env.dep_graph)
      }
  
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      (Prims.string Prims.list,(FStar_Syntax_Syntax.modul,Prims.int)
                                 FStar_Pervasives_Native.tuple2 Prims.list,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun remaining  ->
    fun env  ->
      let uu____1402 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1440 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl  in
            (match uu____1440 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1505 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl  in
            (match uu____1505 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env))  in
      match uu____1402 with
      | (remaining1,(nmods,env1)) -> (remaining1, nmods, env1)
  
let rec (tc_fold_interleave :
  ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
     Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string Prims.list ->
      ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun acc  ->
    fun remaining  ->
      match remaining with
      | [] -> acc
      | uu____1689 ->
          let uu____1692 = acc  in
          (match uu____1692 with
           | (mods,env) ->
               let uu____1727 = tc_one_file_from_remaining remaining env  in
               (match uu____1727 with
                | (remaining1,nmods,env1) ->
                    tc_fold_interleave ((FStar_List.append mods nmods), env1)
                      remaining1))
  
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2)
  =
  fun filenames  ->
    fun dep_graph1  ->
      (let uu____1802 = FStar_Options.debug_any ()  in
       if uu____1802
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____1805 =
             let uu____1806 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____1806  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____1805))
       else ());
      (let env = init_env dep_graph1  in
       let uu____1815 = tc_fold_interleave ([], env) filenames  in
       match uu____1815 with
       | (all_mods,env1) ->
           ((let uu____1861 =
               (FStar_Options.interactive ()) &&
                 (let uu____1863 = FStar_Errors.get_err_count ()  in
                  uu____1863 = (Prims.parse_int "0"))
                in
             if uu____1861
             then
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ()
             else
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                 ());
            (all_mods, env1)))
  