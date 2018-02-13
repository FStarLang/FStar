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
                  then FStar_Pervasives_Native.Some (tcmod, mii)
                  else
                    ((let uu____827 = FStar_Options.debug_any ()  in
                      if uu____827
                      then
                        ((let uu____829 =
                            FStar_Util.string_of_int
                              (FStar_List.length digest')
                             in
                          let uu____834 =
                            FStar_Parser_Dep.print_digest digest'  in
                          let uu____835 =
                            FStar_Util.string_of_int
                              (FStar_List.length digest)
                             in
                          let uu____840 =
                            FStar_Parser_Dep.print_digest digest  in
                          FStar_Util.print4
                            "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                            uu____829 uu____834 uu____835 uu____840);
                         if
                           (FStar_List.length digest) =
                             (FStar_List.length digest')
                         then
                           FStar_List.iter2
                             (fun uu____865  ->
                                fun uu____866  ->
                                  match (uu____865, uu____866) with
                                  | ((x,y),(x',y')) ->
                                      if (x <> x) || (y <> y')
                                      then
                                        let uu____895 =
                                          FStar_Parser_Dep.print_digest
                                            [(x, y)]
                                           in
                                        let uu____904 =
                                          FStar_Parser_Dep.print_digest
                                            [(x', y')]
                                           in
                                        FStar_Util.print2
                                          "Differ at: Expected %s\n Got %s\n"
                                          uu____895 uu____904
                                      else ()) digest digest'
                         else ())
                      else ());
                     fail1 "Stale")
              | uu____916 -> fail1 "Stale")
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
            let uu____939 =
              FStar_Parser_Dep.all_cmd_line_files
                env.FStar_TypeChecker_Env.dep_graph
               in
            FStar_Parser_Dep.cache_file_name uu____939 fn  in
          FStar_Util.print1 "Storing module to cache: %s\n\n" cache_file;
          (let digest =
             FStar_Parser_Dep.hash_dependences
               env.FStar_TypeChecker_Env.dep_graph fn
              in
           match digest with
           | FStar_Pervasives_Native.Some hashes ->
               FStar_Util.save_value_to_file cache_file (hashes, modul, mii)
           | uu____983 ->
               let uu____992 =
                 let uu____993 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 let uu____994 =
                   FStar_Range.mk_pos (Prims.parse_int "0")
                     (Prims.parse_int "0")
                    in
                 FStar_Range.mk_range fn uu____993 uu____994  in
               let uu____995 =
                 let uu____1000 =
                   FStar_Util.format1
                     "%s was not written, since some of its dependences were not also checked"
                     cache_file
                    in
                 (FStar_Errors.Warning_FileNotWritten, uu____1000)  in
               FStar_Errors.log_issue uu____992 uu____995)
  
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
        (let tc_source_file uu____1044 =
           let uu____1045 = parse env pre_fn fn  in
           match uu____1045 with
           | (fmod,env1) ->
               let check_mod fmod1 uu____1076 =
                 let uu____1077 =
                   FStar_Util.record_time
                     (fun uu____1091  ->
                        FStar_TypeChecker_Tc.check_module env1 fmod1)
                    in
                 match uu____1077 with
                 | ((tcmod,env2),time) -> ((tcmod, time), env2)  in
               let uu____1111 =
                 let uu____1120 =
                   let uu____1125 =
                     let uu____1126 =
                       FStar_Parser_Dep.all_cmd_line_files
                         env1.FStar_TypeChecker_Env.dep_graph
                        in
                     FStar_Parser_Dep.check_or_use_extracted_interface
                       uu____1126 fn
                      in
                   if uu____1125
                   then
                     (FStar_Util.print1
                        "Extracting interface for: %s, will be using it for type checking/caching\n\n"
                        (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str;
                      (let uu____1134 =
                         FStar_Parser_Dep.interface_filename fn  in
                       let uu____1135 =
                         FStar_TypeChecker_Tc.extract_interface env1 fmod  in
                       (uu____1134, uu____1135)))
                   else (fn, fmod)  in
                 match uu____1120 with
                 | (fn1,fmod1) ->
                     let uu____1147 =
                       (FStar_Options.should_verify
                          (fmod1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                         &&
                         ((FStar_Options.record_hints ()) ||
                            (FStar_Options.use_hints ()))
                        in
                     if uu____1147
                     then
                       let uu____1156 = FStar_Parser_ParseIt.find_file fn1
                          in
                       FStar_SMTEncoding_Solver.with_hints_db uu____1156
                         (check_mod fmod1)
                     else check_mod fmod1 ()
                  in
               (match uu____1111 with
                | (tcmod,env2) ->
                    let mii =
                      FStar_ToSyntax_Env.inclusion_info
                        env2.FStar_TypeChecker_Env.dsenv
                        (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name
                       in
                    (tcmod, mii, env2))
            in
         let uu____1191 = FStar_Options.cache_checked_modules ()  in
         if uu____1191
         then
           let uu____1200 = load_module_from_cache env fn  in
           match uu____1200 with
           | FStar_Pervasives_Native.None  ->
               let uu____1219 = tc_source_file ()  in
               (match uu____1219 with
                | (tcmod,mii,env1) ->
                    ((let uu____1250 =
                        (let uu____1253 = FStar_Errors.get_err_count ()  in
                         uu____1253 = (Prims.parse_int "0")) &&
                          ((FStar_Options.lax ()) ||
                             (FStar_Options.should_verify
                                ((FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name).FStar_Ident.str))
                         in
                      if uu____1250
                      then
                        store_module_to_cache env1 fn
                          (FStar_Pervasives_Native.fst tcmod) mii
                      else ());
                     (tcmod, env1)))
           | FStar_Pervasives_Native.Some (tcmod,mii) ->
               let uu____1265 =
                 let uu____1270 =
                   FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii
                     (FStar_TypeChecker_Normalize.erase_universes env)
                    in
                 FStar_All.pipe_left (with_tcenv env) uu____1270  in
               (match uu____1265 with
                | (uu____1291,env1) ->
                    let env2 =
                      FStar_TypeChecker_Tc.load_checked_module env1 tcmod  in
                    ((tcmod, (Prims.parse_int "0")), env2))
         else
           (let uu____1299 = tc_source_file ()  in
            match uu____1299 with | (tcmod,uu____1319,env1) -> (tcmod, env1)))
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____1342 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____1342 ["fsti"; "fsi"]))
        &&
        (let uu____1344 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____1344 ["fst"; "fs"])
  
let (pop_context : FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit) =
  fun env  ->
    fun msg  ->
      (let uu____1352 = FStar_ToSyntax_Env.pop ()  in
       FStar_All.pipe_right uu____1352 FStar_Pervasives.ignore);
      (let uu____1354 = FStar_TypeChecker_Env.pop env msg  in
       FStar_All.pipe_right uu____1354 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv  in
      let env1 = FStar_TypeChecker_Env.push env msg  in
      let uu___54_1363 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___54_1363.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___54_1363.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___54_1363.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___54_1363.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___54_1363.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___54_1363.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___54_1363.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___54_1363.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___54_1363.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___54_1363.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___54_1363.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___54_1363.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___54_1363.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___54_1363.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___54_1363.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___54_1363.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___54_1363.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___54_1363.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___54_1363.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___54_1363.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___54_1363.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___54_1363.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___54_1363.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___54_1363.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___54_1363.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___54_1363.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___54_1363.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___54_1363.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___54_1363.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___54_1363.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___54_1363.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___54_1363.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___54_1363.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv;
        FStar_TypeChecker_Env.dep_graph =
          (uu___54_1363.FStar_TypeChecker_Env.dep_graph)
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
      let uu____1388 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1426 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl  in
            (match uu____1426 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1491 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl  in
            (match uu____1491 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env))  in
      match uu____1388 with
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
      | uu____1675 ->
          let uu____1678 = acc  in
          (match uu____1678 with
           | (mods,env) ->
               let uu____1713 = tc_one_file_from_remaining remaining env  in
               (match uu____1713 with
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
      (let uu____1788 = FStar_Options.debug_any ()  in
       if uu____1788
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____1791 =
             let uu____1792 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____1792  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____1791))
       else ());
      (let env = init_env dep_graph1  in
       let uu____1801 = tc_fold_interleave ([], env) filenames  in
       match uu____1801 with
       | (all_mods,env1) ->
           ((let uu____1847 =
               (FStar_Options.interactive ()) &&
                 (let uu____1849 = FStar_Errors.get_err_count ()  in
                  uu____1849 = (Prims.parse_int "0"))
                in
             if uu____1847
             then
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ()
             else
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                 ());
            (all_mods, env1)))
  