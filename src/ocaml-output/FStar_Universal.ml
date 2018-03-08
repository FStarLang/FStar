open Prims
let (cache_version_number : Prims.int) = (Prims.parse_int "1") 
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
      'a FStar_Syntax_DsEnv.withenv ->
        ('a,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____47 = f env.FStar_TypeChecker_Env.dsenv  in
      match uu____47 with
      | (a,dsenv1) ->
          (a,
            (let uu___51_61 = env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___51_61.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___51_61.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___51_61.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___51_61.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___51_61.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___51_61.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___51_61.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___51_61.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___51_61.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___51_61.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___51_61.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___51_61.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___51_61.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___51_61.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___51_61.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___51_61.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___51_61.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___51_61.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___51_61.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___51_61.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___51_61.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___51_61.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.tc_term =
                 (uu___51_61.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___51_61.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___51_61.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___51_61.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___51_61.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___51_61.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___51_61.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___51_61.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.splice =
                 (uu___51_61.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___51_61.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___51_61.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___51_61.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv1;
               FStar_TypeChecker_Env.dep_graph =
                 (uu___51_61.FStar_TypeChecker_Env.dep_graph)
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
                             | (uu____190,env1) ->
                                 let uu____192 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true
                                    in
                                 FStar_All.pipe_left (with_tcenv env1)
                                   uu____192)
                        | uu____205 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n")))
               in
            (match uu____112 with
             | (ast1,env1) ->
                 let uu____220 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1  in
                 FStar_All.pipe_left (with_tcenv env1) uu____220)
  
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps  ->
    let solver1 =
      let uu____237 = FStar_Options.lax ()  in
      if uu____237
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___52_239 = FStar_SMTEncoding_Solver.solver  in
         {
           FStar_TypeChecker_Env.init =
             (uu___52_239.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___52_239.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___52_239.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.encode_modul =
             (uu___52_239.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___52_239.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___52_239.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___52_239.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___52_239.FStar_TypeChecker_Env.refresh)
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
      let uu___53_242 = env  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___53_242.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___53_242.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___53_242.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___53_242.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___53_242.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___53_242.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___53_242.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___53_242.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___53_242.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___53_242.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___53_242.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___53_242.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___53_242.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___53_242.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___53_242.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___53_242.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___53_242.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___53_242.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___53_242.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___53_242.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___53_242.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___53_242.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___53_242.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___53_242.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___53_242.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___53_242.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___53_242.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___53_242.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___53_242.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.splice =
          (uu___53_242.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___53_242.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___53_242.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___53_242.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___53_242.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___53_242.FStar_TypeChecker_Env.dep_graph)
      }  in
    let env2 =
      let uu___54_244 = env1  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___54_244.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___54_244.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___54_244.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___54_244.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___54_244.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___54_244.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___54_244.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___54_244.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___54_244.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___54_244.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___54_244.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___54_244.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___54_244.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___54_244.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___54_244.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___54_244.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___54_244.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___54_244.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___54_244.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___54_244.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___54_244.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___54_244.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___54_244.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___54_244.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___54_244.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___54_244.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___54_244.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___54_244.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___54_244.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___54_244.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.splice =
          (uu___54_244.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___54_244.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___54_244.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___54_244.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___54_244.FStar_TypeChecker_Env.dep_graph)
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
          let uu____269 =
            let uu____270 =
              let uu____271 = FStar_Options.file_list ()  in
              FStar_List.hd uu____271  in
            FStar_Parser_Dep.lowercase_module_name uu____270  in
          let uu____274 =
            let uu____275 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name  in
            FStar_String.lowercase uu____275  in
          uu____269 = uu____274  in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____280,{ FStar_Parser_AST.d = uu____281;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____283;
                           FStar_Parser_AST.quals = uu____284;
                           FStar_Parser_AST.attrs = uu____285;_}::uu____286)
              -> d
          | FStar_Parser_AST.Interface
              (uu____293,{ FStar_Parser_AST.d = uu____294;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____296;
                           FStar_Parser_AST.quals = uu____297;
                           FStar_Parser_AST.attrs = uu____298;_}::uu____299,uu____300)
              -> d
          | uu____307 -> FStar_Range.dummyRange  in
        let uu____308 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____308 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____320 =
              let uu____325 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false
                 in
              FStar_All.pipe_left (with_tcenv env) uu____325  in
            (match uu____320 with
             | (ast_modul1,env1) ->
                 let uu____346 =
                   let uu____351 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1
                      in
                   FStar_All.pipe_left (with_tcenv env1) uu____351  in
                 (match uu____346 with
                  | (modul,env2) ->
                      ((let uu____373 =
                          let uu____374 = acceptable_mod_name modul  in
                          Prims.op_Negation uu____374  in
                        if uu____373
                        then
                          let msg =
                            let uu____376 =
                              let uu____377 =
                                let uu____378 = FStar_Options.file_list ()
                                   in
                                FStar_List.hd uu____378  in
                              FStar_Parser_Dep.module_name_of_file uu____377
                               in
                            FStar_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu____376
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu____382 =
                          let uu____391 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv
                             in
                          if uu____391
                          then (modul, [], env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul
                           in
                        match uu____382 with
                        | (modul1,uu____410,env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____427 = FStar_List.hd ast_decls  in
                 (match uu____427 with
                  | { FStar_Parser_AST.d = uu____434;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____436;
                      FStar_Parser_AST.quals = uu____437;
                      FStar_Parser_AST.attrs = uu____438;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu____448 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____466 =
                            let uu____473 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl
                               in
                            FStar_All.pipe_left (with_tcenv env1) uu____473
                             in
                          match uu____466 with
                          | (decls,env2) -> (env2, decls)) env ast_decls
                    in
                 (match uu____448 with
                  | (env1,ast_decls_l) ->
                      let uu____524 =
                        let uu____529 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l)
                           in
                        FStar_All.pipe_left (with_tcenv env1) uu____529  in
                      (match uu____524 with
                       | (sigelts,env2) ->
                           let uu____550 =
                             let uu____559 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv
                                in
                             if uu____559
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts
                              in
                           (match uu____550 with
                            | (modul1,uu____578,env3) ->
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
           (l,decls,uu____595)),uu____596)
          ->
          let uu____621 =
            let uu____626 =
              FStar_ToSyntax_Interleave.initialize_interface l decls  in
            FStar_All.pipe_left (with_tcenv env) uu____626  in
          FStar_Pervasives_Native.snd uu____621
      | FStar_Parser_ParseIt.ASTFragment uu____639 ->
          let uu____650 =
            let uu____655 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name
               in
            (FStar_Errors.Fatal_ParseErrors, uu____655)  in
          FStar_Errors.raise_err uu____650
      | FStar_Parser_ParseIt.ParseError (err,msg,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, rng))
      | FStar_Parser_ParseIt.Term uu____659 ->
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
  fun env  ->
    fun fn  ->
      let cache_file = FStar_Parser_Dep.cache_file_name fn  in
      let fail1 tag =
        invalidate_cache ();
        (let uu____749 =
           let uu____750 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
              in
           let uu____751 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0")
              in
           FStar_Range.mk_range fn uu____750 uu____751  in
         let uu____752 =
           let uu____757 =
             FStar_Util.format3
               "%s cache file %s; will recheck %s and all subsequent files"
               tag cache_file fn
              in
           (FStar_Errors.Warning_CachedFile, uu____757)  in
         FStar_Errors.log_issue uu____749 uu____752);
        FStar_Pervasives_Native.None  in
      let uu____766 = FStar_ST.op_Bang some_cache_invalid  in
      match uu____766 with
      | FStar_Pervasives_Native.Some uu____824 ->
          FStar_Pervasives_Native.None
      | uu____833 ->
          if FStar_Util.file_exists cache_file
          then
            let uu____846 = FStar_Util.load_value_from_file cache_file  in
            (match uu____846 with
             | FStar_Pervasives_Native.None  -> fail1 "Corrupt"
             | FStar_Pervasives_Native.Some
                 (vnum,digest,tcmod,tcmod_iface_opt,mii) ->
                 if vnum <> cache_version_number
                 then fail1 "Stale, because inconsistent cache version"
                 else
                   (let uu____963 =
                      FStar_Parser_Dep.hash_dependences
                        env.FStar_TypeChecker_Env.dep_graph fn
                       in
                    match uu____963 with
                    | FStar_Pervasives_Native.Some digest' ->
                        if digest = digest'
                        then
                          FStar_Pervasives_Native.Some
                            (tcmod, tcmod_iface_opt, mii)
                        else
                          ((let uu____1023 = FStar_Options.debug_any ()  in
                            if uu____1023
                            then
                              ((let uu____1025 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length digest')
                                   in
                                let uu____1030 =
                                  FStar_Parser_Dep.print_digest digest'  in
                                let uu____1031 =
                                  FStar_Util.string_of_int
                                    (FStar_List.length digest)
                                   in
                                let uu____1036 =
                                  FStar_Parser_Dep.print_digest digest  in
                                FStar_Util.print4
                                  "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                                  uu____1025 uu____1030 uu____1031 uu____1036);
                               if
                                 (FStar_List.length digest) =
                                   (FStar_List.length digest')
                               then
                                 FStar_List.iter2
                                   (fun uu____1061  ->
                                      fun uu____1062  ->
                                        match (uu____1061, uu____1062) with
                                        | ((x,y),(x',y')) ->
                                            if (x <> x') || (y <> y')
                                            then
                                              let uu____1091 =
                                                FStar_Parser_Dep.print_digest
                                                  [(x, y)]
                                                 in
                                              let uu____1100 =
                                                FStar_Parser_Dep.print_digest
                                                  [(x', y')]
                                                 in
                                              FStar_Util.print2
                                                "Differ at: Expected %s\n Got %s\n"
                                                uu____1091 uu____1100
                                            else ()) digest digest'
                               else ())
                            else ());
                           fail1 "Stale")
                    | uu____1112 -> fail1 "Stale"))
          else fail1 "Absent"
  
let (store_module_to_cache :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.modul ->
        FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
          FStar_Syntax_DsEnv.module_inclusion_info -> Prims.unit)
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
            | uu____1190 ->
                let uu____1199 =
                  let uu____1200 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  let uu____1201 =
                    FStar_Range.mk_pos (Prims.parse_int "0")
                      (Prims.parse_int "0")
                     in
                  FStar_Range.mk_range fn uu____1200 uu____1201  in
                let uu____1202 =
                  let uu____1207 =
                    FStar_Util.format1
                      "%s was not written, since some of its dependences were not also checked"
                      cache_file
                     in
                  (FStar_Errors.Warning_FileNotWritten, uu____1207)  in
                FStar_Errors.log_issue uu____1199 uu____1202
  
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
        (let tc_source_file uu____1255 =
           let uu____1256 = parse env pre_fn fn  in
           match uu____1256 with
           | (fmod,env1) ->
               let check_mod uu____1292 =
                 let uu____1293 =
                   FStar_Util.record_time
                     (fun uu____1315  ->
                        FStar_TypeChecker_Tc.check_module env1 fmod)
                    in
                 match uu____1293 with
                 | ((tcmod,tcmod_iface_opt,env2),time) ->
                     ((tcmod, time), tcmod_iface_opt, env2)
                  in
               let uu____1350 =
                 let uu____1363 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                    in
                 if uu____1363
                 then
                   let uu____1376 = FStar_Parser_ParseIt.find_file fn  in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1376
                     check_mod
                 else check_mod ()  in
               (match uu____1350 with
                | (tcmod,tcmod_iface_opt,env2) ->
                    let mii =
                      FStar_Syntax_DsEnv.inclusion_info
                        env2.FStar_TypeChecker_Env.dsenv
                        (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name
                       in
                    (tcmod, tcmod_iface_opt, mii, env2))
            in
         let uu____1426 = FStar_Options.cache_checked_modules ()  in
         if uu____1426
         then
           let uu____1435 = load_module_from_cache env fn  in
           match uu____1435 with
           | FStar_Pervasives_Native.None  ->
               let uu____1462 = tc_source_file ()  in
               (match uu____1462 with
                | (tcmod,tcmod_iface_opt,mii,env1) ->
                    ((let uu____1502 =
                        (let uu____1505 = FStar_Errors.get_err_count ()  in
                         uu____1505 = (Prims.parse_int "0")) &&
                          ((FStar_Options.lax ()) ||
                             (FStar_Options.should_verify
                                ((FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name).FStar_Ident.str))
                         in
                      if uu____1502
                      then
                        store_module_to_cache env1 fn
                          (FStar_Pervasives_Native.fst tcmod) tcmod_iface_opt
                          mii
                      else ());
                     (tcmod, env1)))
           | FStar_Pervasives_Native.Some (tcmod,tcmod_iface_opt,mii) ->
               let tcmod1 =
                 if tcmod.FStar_Syntax_Syntax.is_interface
                 then tcmod
                 else
                   (let uu____1528 =
                      FStar_Options.use_extracted_interfaces ()  in
                    if uu____1528
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
               let uu____1535 =
                 let uu____1540 =
                   FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1 mii
                     (FStar_TypeChecker_Normalize.erase_universes env)
                    in
                 FStar_All.pipe_left (with_tcenv env) uu____1540  in
               (match uu____1535 with
                | (uu____1561,env1) ->
                    let env2 =
                      FStar_TypeChecker_Tc.load_checked_module env1 tcmod1
                       in
                    ((tcmod1, (Prims.parse_int "0")), env2))
         else
           (let uu____1569 = tc_source_file ()  in
            match uu____1569 with
            | (tcmod,tcmod_iface_opt,uu____1594,env1) ->
                let tcmod1 =
                  if FStar_Util.is_some tcmod_iface_opt
                  then
                    let uu____1617 =
                      FStar_All.pipe_right tcmod_iface_opt FStar_Util.must
                       in
                    (uu____1617, (FStar_Pervasives_Native.snd tcmod))
                  else tcmod  in
                (tcmod1, env1)))
  
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf  in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl  in
      ((m1 = m2) &&
         (let uu____1634 = FStar_Util.get_file_extension intf  in
          FStar_List.mem uu____1634 ["fsti"; "fsi"]))
        &&
        (let uu____1636 = FStar_Util.get_file_extension impl  in
         FStar_List.mem uu____1636 ["fst"; "fs"])
  
let (pop_context : FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit) =
  fun env  ->
    fun msg  ->
      let uu____1643 = FStar_TypeChecker_Tc.pop_context env msg  in
      FStar_All.pipe_right uu____1643 FStar_Pervasives.ignore
  
let (push_context :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env) =
  fun env  -> fun msg  -> FStar_TypeChecker_Tc.push_context env msg 
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      (Prims.string Prims.list,(FStar_Syntax_Syntax.modul,Prims.int)
                                 FStar_Pervasives_Native.tuple2 Prims.list,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3)
  =
  fun remaining  ->
    fun env  ->
      let uu____1674 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1712 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl  in
            (match uu____1712 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1777 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl  in
            (match uu____1777 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env))  in
      match uu____1674 with
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
      | uu____1961 ->
          let uu____1964 = acc  in
          (match uu____1964 with
           | (mods,env) ->
               let uu____1999 = tc_one_file_from_remaining remaining env  in
               (match uu____1999 with
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
      (let uu____2074 = FStar_Options.debug_any ()  in
       if uu____2074
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____2077 =
             let uu____2078 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file)
                in
             FStar_String.concat " " uu____2078  in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____2077))
       else ());
      (let env = init_env dep_graph1  in
       let uu____2087 = tc_fold_interleave ([], env) filenames  in
       match uu____2087 with
       | (all_mods,env1) ->
           ((let uu____2133 =
               (FStar_Options.interactive ()) &&
                 (let uu____2135 = FStar_Errors.get_err_count ()  in
                  uu____2135 = (Prims.parse_int "0"))
                in
             if uu____2133
             then
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ()
             else
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                 ());
            (all_mods, env1)))
  