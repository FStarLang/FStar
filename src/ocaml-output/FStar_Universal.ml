open Prims
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul ->
    (Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2)
  =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
  
let with_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_ToSyntax_Env.withenv ->
        ('a,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____32 = f env.FStar_TypeChecker_Env.dsenv  in
      match uu____32 with
      | (a,dsenv) ->
          (a,
            (let uu___51_46 = env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___51_46.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___51_46.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___51_46.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___51_46.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___51_46.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___51_46.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___51_46.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___51_46.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___51_46.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___51_46.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___51_46.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___51_46.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___51_46.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___51_46.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___51_46.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___51_46.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___51_46.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___51_46.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___51_46.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___51_46.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___51_46.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___51_46.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.tc_term =
                 (uu___51_46.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___51_46.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___51_46.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___51_46.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___51_46.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___51_46.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___51_46.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___51_46.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___51_46.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___51_46.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___51_46.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv;
               FStar_TypeChecker_Env.dep_graph =
                 (uu___51_46.FStar_TypeChecker_Env.dep_graph)
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
        let uu____68 = FStar_Parser_Driver.parse_file fn  in
        match uu____68 with
        | (ast,uu____84) ->
            let uu____97 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____107 = FStar_Parser_Driver.parse_file pre_fn1  in
                  (match uu____107 with
                   | (pre_ast,uu____123) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____142),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____153 =
                              let uu____158 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1
                                 in
                              FStar_All.pipe_left (with_tcenv env) uu____158
                               in
                            (match uu____153 with
                             | (uu____175,env1) ->
                                 let uu____177 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 FStar_All.pipe_left (with_tcenv env1)
                                   uu____177)
                        | uu____190 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____97 with
             | (ast1,env1) ->
                 let uu____205 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 FStar_All.pipe_left (with_tcenv env1) uu____205)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____222 = FStar_Options.lax ()  in
      if uu____222
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___52_224 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___52_224.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___52_224.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___52_224.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.encode_modul =
             (uu___52_224.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___52_224.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___52_224.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___52_224.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___52_224.FStar_TypeChecker_Env.refresh)
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
      let uu___53_227 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___53_227.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___53_227.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___53_227.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___53_227.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___53_227.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___53_227.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___53_227.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___53_227.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___53_227.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___53_227.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___53_227.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___53_227.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___53_227.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___53_227.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___53_227.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___53_227.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___53_227.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___53_227.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___53_227.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___53_227.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___53_227.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___53_227.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___53_227.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___53_227.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___53_227.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___53_227.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___53_227.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___53_227.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___53_227.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___53_227.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___53_227.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___53_227.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___53_227.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___53_227.FStar_TypeChecker_Env.dep_graph)
      }  in
    let env2 =
      let uu___54_229 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___54_229.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___54_229.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___54_229.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___54_229.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___54_229.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___54_229.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___54_229.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___54_229.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___54_229.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___54_229.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___54_229.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___54_229.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___54_229.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___54_229.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___54_229.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___54_229.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___54_229.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___54_229.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___54_229.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___54_229.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___54_229.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___54_229.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___54_229.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___54_229.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___54_229.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___54_229.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___54_229.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___54_229.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___54_229.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___54_229.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___54_229.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___54_229.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___54_229.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___54_229.FStar_TypeChecker_Env.dep_graph)
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
          let uu____254 =
            let uu____255 =
              let uu____256 = FStar_Options.file_list ()  in
              FStar_List.hd uu____256  in
            FStar_Parser_Dep.lowercase_module_name uu____255  in
          let uu____259 =
            let uu____260 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____260  in
          uu____254 = uu____259  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____265,{ FStar_Parser_AST.d = uu____266;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____268;
                           FStar_Parser_AST.quals = uu____269;
                           FStar_Parser_AST.attrs = uu____270;_}::uu____271)
              -> d
          | FStar_Parser_AST.Interface
              (uu____278,{ FStar_Parser_AST.d = uu____279;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____281;
                           FStar_Parser_AST.quals = uu____282;
                           FStar_Parser_AST.attrs = uu____283;_}::uu____284,uu____285)
              -> d
          | uu____292 -> FStar_Range.dummyRange  in
        let uu____293 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____293 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____305 =
              let uu____310 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_tcenv env) uu____310  in
            (match uu____305 with
             | (ast_modul1,env1) ->
                 let uu____331 =
                   let uu____336 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_tcenv env1) uu____336  in
                 (match uu____331 with
                  | (modul,env2) ->
                      ((let uu____358 =
                          let uu____359 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____359  in
                        if uu____358
                        then
                          let msg =
                            let uu____361 =
                              let uu____362 =
                                let uu____363 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____363  in
                              FStar_Parser_Dep.module_name_of_file uu____362
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____361
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____367 =
                          let uu____376 =
                            FStar_ToSyntax_Env.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____376
                          then (modul, [], env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul
                              false
                           in
                        match uu____367 with
                        | (modul1,uu____395,env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____412 = FStar_List.hd ast_decls  in
                 (match uu____412 with
                  | { FStar_Parser_AST.d = uu____419;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____421;
                      FStar_Parser_AST.quals = uu____422;
                      FStar_Parser_AST.attrs = uu____423;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____433 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____451 =
                            let uu____458 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_tcenv env1) uu____458
                             in
                          match uu____451 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____433 with
                  | (env1,ast_decls_l) ->
                      let uu____509 =
                        let uu____514 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_tcenv env1) uu____514  in
                      (match uu____509 with
                       | (sigelts,env2) ->
                           let uu____535 =
                             let uu____544 =
                               FStar_ToSyntax_Env.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____544
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____535 with
                            | (modul1,uu____563,env3) ->
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
           (l,decls,uu____580)),uu____581)
          ->
          let uu____606 =
            let uu____611 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_tcenv env) uu____611  in
          FStar_Pervasives_Native.snd uu____606
      | FStar_Parser_ParseIt.ASTFragment uu____624 ->
          let uu____635 =
            let uu____640 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____640)  in
          FStar_Errors.raise_err uu____635
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____644 ->
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
        let uu____664 =
          FStar_Parser_Dep.all_cmd_line_files
            env.FStar_TypeChecker_Env.dep_graph
           in
        FStar_Parser_Dep.cache_file_name uu____664 fn  in
      let fail1 tag =
        (let uu____678 =
           let uu____679 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
              in
           let uu____680 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
              in
           FStar_Range.mk_range fn uu____679 uu____680  in
         let uu____681 =
           let uu____686 =
             FStar_Util.format3 "%s cache file %s; will recheck %s" tag
               cache_file fn
              in
           (FStar_Errors.Warning_CachedFile, uu____686)  in
         FStar_Errors.log_issue uu____678 uu____681);
        FStar_Pervasives_Native.None  in
      if FStar_Util.file_exists cache_file
      then
        let uu____697 = FStar_Util.load_value_from_file cache_file  in
        match uu____697 with
        | FStar_Pervasives_Native.None  -> fail1 "Corrupt"
        | FStar_Pervasives_Native.Some (digest,tcmod,mii) ->
            let uu____769 =
              FStar_Parser_Dep.hash_dependences
                env.FStar_TypeChecker_Env.dep_graph fn
               in
            (match uu____769 with
             | FStar_Pervasives_Native.Some digest' ->
                 if digest = digest'
                 then FStar_Pervasives_Native.Some (tcmod, mii)
                 else
                   ((let uu____815 = FStar_Options.debug_any ()  in
                     if uu____815
                     then
                       ((let uu____817 =
                           FStar_Util.string_of_int
                             (FStar_List.length digest')
                            in
                         let uu____822 =
                           FStar_Parser_Dep.print_digest digest'  in
                         let uu____823 =
                           FStar_Util.string_of_int
                             (FStar_List.length digest)
                            in
                         let uu____828 = FStar_Parser_Dep.print_digest digest
                            in
                         FStar_Util.print4
                           "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                           uu____817 uu____822 uu____823 uu____828);
                        if
                          (FStar_List.length digest) =
                            (FStar_List.length digest')
                        then
                          FStar_List.iter2
                            (fun uu____853  ->
                               fun uu____854  ->
                                 match (uu____853, uu____854) with
                                 | ((x,y),(x',y')) ->
                                     if (x <> x) || (y <> y')
                                     then
                                       let uu____883 =
                                         FStar_Parser_Dep.print_digest
                                           [(x, y)]
                                          in
                                       let uu____892 =
                                         FStar_Parser_Dep.print_digest
                                           [(x', y')]
                                          in
                                       FStar_Util.print2
                                         "Differ at: Expected %s\n Got %s\n"
                                         uu____883 uu____892
                                     else ()) digest digest'
                        else ())
                     else ());
                    fail1 "Stale")
             | uu____904 -> fail1 "Stale")
      else fail1 "Absent"
  
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
            let uu____927 =
              FStar_Parser_Dep.all_cmd_line_files
                env.FStar_TypeChecker_Env.dep_graph
               in
            FStar_Parser_Dep.cache_file_name uu____927 fn  in
          let digest =
            FStar_Parser_Dep.hash_dependences
              env.FStar_TypeChecker_Env.dep_graph fn
             in
          match digest with
          | FStar_Pervasives_Native.Some hashes ->
              FStar_Util.save_value_to_file cache_file (hashes, modul, mii)
          | uu____970 ->
              let uu____979 =
                let uu____980 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                let uu____981 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0")
                   in
                FStar_Range.mk_range fn uu____980 uu____981  in
              let uu____982 =
                let uu____987 =
                  FStar_Util.format1
                    "%s was not written, since some of its dependences were not also checked"
                    cache_file
                   in
                (FStar_Errors.Warning_FileNotWritten, uu____987)  in
              FStar_Errors.log_issue uu____979 uu____982
  
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
        (let tc_source_file uu____1031 =
           let uu____1032 = parse env pre_fn fn  in
           match uu____1032 with
           | (fmod,env1) ->
               let check_mod fmod1 uu____1063 =
                 let uu____1064 =
                   FStar_Util.record_time
                     (fun uu____1078  ->
                        FStar_TypeChecker_Tc.check_module env1 fmod1)
                    in
                 match uu____1064 with
                 | ((tcmod,env2),time) -> ((tcmod, time), env2)  in
               let uu____1098 =
                 let uu____1107 =
                   let uu____1114 =
                     let uu____1115 =
                       FStar_Parser_Dep.all_cmd_line_files
                         env1.FStar_TypeChecker_Env.dep_graph
                        in
                     FStar_Parser_Dep.check_or_use_extracted_interface
                       uu____1115 fn
                      in
                   if uu____1114
                   then
                     let uu____1124 =
                       FStar_TypeChecker_Tc.extract_interface env1 fmod  in
                     (true, uu____1124,
                       (let uu___55_1126 = env1  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___55_1126.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___55_1126.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___55_1126.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___55_1126.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___55_1126.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___55_1126.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___55_1126.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___55_1126.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___55_1126.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___55_1126.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___55_1126.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___55_1126.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___55_1126.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level =
                            (uu___55_1126.FStar_TypeChecker_Env.top_level);
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___55_1126.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___55_1126.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface = true;
                          FStar_TypeChecker_Env.admit =
                            (uu___55_1126.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___55_1126.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___55_1126.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.failhard =
                            (uu___55_1126.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___55_1126.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___55_1126.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___55_1126.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___55_1126.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___55_1126.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___55_1126.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qname_and_index =
                            (uu___55_1126.FStar_TypeChecker_Env.qname_and_index);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___55_1126.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth =
                            (uu___55_1126.FStar_TypeChecker_Env.synth);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___55_1126.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___55_1126.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___55_1126.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___55_1126.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.dep_graph =
                            (uu___55_1126.FStar_TypeChecker_Env.dep_graph)
                        }))
                   else (false, fmod, env1)  in
                 match uu____1107 with
                 | (checking_or_using_extracted_interface,fmod1,env2) ->
                     let uu____1139 =
                       (FStar_Options.should_verify
                          (fmod1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                         &&
                         ((FStar_Options.record_hints ()) ||
                            (FStar_Options.use_hints ()))
                        in
                     if uu____1139
                     then
                       let uu____1148 = FStar_Parser_ParseIt.find_file fn  in
                       FStar_SMTEncoding_Solver.with_hints_db uu____1148
                         checking_or_using_extracted_interface
                         (check_mod fmod1)
                     else check_mod fmod1 ()
                  in
               (match uu____1098 with
                | (tcmod,env2) ->
                    let mii =
                      FStar_ToSyntax_Env.inclusion_info
                        env2.FStar_TypeChecker_Env.dsenv
                        (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name
                       in
                    (tcmod, mii, env2))
            in
         let uu____1183 = FStar_Options.cache_checked_modules ()  in
         if uu____1183
         then
           let uu____1192 = load_module_from_cache env fn  in
           match uu____1192 with
           | FStar_Pervasives_Native.None  ->
               let uu____1211 = tc_source_file ()  in
               (match uu____1211 with
                | (tcmod,mii,env1) ->
                    ((let uu____1242 =
                        (let uu____1245 = FStar_Errors.get_err_count ()  in
                         uu____1245 = (Prims.parse_int "0")) &&
                          ((FStar_Options.lax ()) ||
                             (FStar_Options.should_verify
                                ((FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name).FStar_Ident.str))
                         in
                      if uu____1242
                      then
                        store_module_to_cache env1 fn
                          (FStar_Pervasives_Native.fst tcmod) mii
                      else ());
                     (tcmod, env1)))
           | FStar_Pervasives_Native.Some (tcmod,mii) ->
               let uu____1257 =
                 let uu____1262 =
                   FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii
                     (FStar_TypeChecker_Normalize.erase_universes env)
                    in
                 FStar_All.pipe_left (with_tcenv env) uu____1262  in
               (match uu____1257 with
                | (uu____1283,env1) ->
                    let env2 =
                      FStar_TypeChecker_Tc.load_checked_module env1 tcmod  in
                    ((tcmod, (Prims.parse_int "0")), env2))
         else
           (let uu____1291 = tc_source_file ()  in
            match uu____1291 with | (tcmod,uu____1311,env1) -> (tcmod, env1)))
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____1334 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____1334 ["fsti"; "fsi"]))
        &&
        (let uu____1336 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____1336 ["fst"; "fs"])
  
let (pop_context : FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit) =
  fun env  ->
    fun msg  ->
      (let uu____1344 = FStar_ToSyntax_Env.pop ()  in
       FStar_All.pipe_right uu____1344 FStar_Pervasives.ignore);
      (let uu____1346 = FStar_TypeChecker_Env.pop env msg  in
       FStar_All.pipe_right uu____1346 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv  in
      let env1 = FStar_TypeChecker_Env.push env msg  in
      let uu___56_1355 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___56_1355.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___56_1355.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___56_1355.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___56_1355.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___56_1355.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___56_1355.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___56_1355.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___56_1355.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___56_1355.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___56_1355.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___56_1355.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___56_1355.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___56_1355.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___56_1355.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___56_1355.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___56_1355.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___56_1355.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___56_1355.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___56_1355.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___56_1355.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___56_1355.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___56_1355.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___56_1355.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___56_1355.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___56_1355.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___56_1355.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___56_1355.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___56_1355.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___56_1355.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___56_1355.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___56_1355.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___56_1355.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___56_1355.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv;
        FStar_TypeChecker_Env.dep_graph =
          (uu___56_1355.FStar_TypeChecker_Env.dep_graph)
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
      let uu____1380 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1418 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl  in
            (match uu____1418 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1483 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl  in
            (match uu____1483 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env))  in
      match uu____1380 with
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
      | uu____1667 ->
          let uu____1670 = acc  in
          (match uu____1670 with
           | (mods,env) ->
               let uu____1705 = tc_one_file_from_remaining remaining env  in
               (match uu____1705 with
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
      (let uu____1780 = FStar_Options.debug_any ()  in
       if uu____1780
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____1783 =
             let uu____1784 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____1784  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____1783))
       else ());
      (let env = init_env dep_graph1  in
       let uu____1793 = tc_fold_interleave ([], env) filenames  in
       match uu____1793 with
       | (all_mods,env1) ->
           ((let uu____1839 =
               (FStar_Options.interactive ()) &&
                 (let uu____1841 = FStar_Errors.get_err_count ()  in
                  uu____1841 = (Prims.parse_int "0"))
                in
             if uu____1839
             then
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ()
             else
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                 ());
            (all_mods, env1)))
  