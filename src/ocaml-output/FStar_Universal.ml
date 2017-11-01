open Prims
let module_or_interface_name:
  FStar_Syntax_Syntax.modul ->
    (Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2
  =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
let user_tactics_modules: Prims.string Prims.list FStar_ST.ref =
  FStar_TypeChecker_Tc.user_tactics_modules
let with_tcenv:
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_ToSyntax_Env.withenv ->
        ('a,FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun f  ->
      let uu____43 = f env.FStar_TypeChecker_Env.dsenv in
      match uu____43 with
      | (a,dsenv) ->
          (a,
            (let uu___522_57 = env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___522_57.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___522_57.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___522_57.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___522_57.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___522_57.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___522_57.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___522_57.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___522_57.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___522_57.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___522_57.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___522_57.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___522_57.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___522_57.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___522_57.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___522_57.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___522_57.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___522_57.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___522_57.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___522_57.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___522_57.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___522_57.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___522_57.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.tc_term =
                 (uu___522_57.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___522_57.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___522_57.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___522_57.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___522_57.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___522_57.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___522_57.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___522_57.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___522_57.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___522_57.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv;
               FStar_TypeChecker_Env.dep_graph =
                 (uu___522_57.FStar_TypeChecker_Env.dep_graph)
             }))
let parse:
  FStar_TypeChecker_Env.env ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        (FStar_Syntax_Syntax.modul,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____79 = FStar_Parser_Driver.parse_file fn in
        match uu____79 with
        | (ast,uu____95) ->
            let uu____108 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____118 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____118 with
                   | (pre_ast,uu____134) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____153),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____164 =
                              let uu____169 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1 in
                              FStar_All.pipe_left (with_tcenv env) uu____169 in
                            (match uu____164 with
                             | (uu____186,env1) ->
                                 let uu____188 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true in
                                 FStar_All.pipe_left (with_tcenv env1)
                                   uu____188)
                        | uu____201 ->
                            FStar_Exn.raise
                              (FStar_Errors.Err
                                 "mismatch between pre-module and module\n"))) in
            (match uu____108 with
             | (ast1,env1) ->
                 let uu____216 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1 in
                 FStar_All.pipe_left (with_tcenv env1) uu____216)
let init_env: FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env =
  fun deps  ->
    let solver1 =
      let uu____233 = FStar_Options.lax () in
      if uu____233
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___523_235 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___523_235.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___523_235.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___523_235.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.encode_modul =
             (uu___523_235.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___523_235.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___523_235.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___523_235.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___523_235.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Parser_Const.prims_lid in
    let env1 =
      let uu___524_238 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___524_238.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___524_238.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___524_238.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___524_238.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___524_238.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___524_238.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___524_238.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___524_238.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___524_238.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___524_238.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___524_238.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___524_238.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___524_238.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___524_238.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___524_238.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___524_238.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___524_238.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___524_238.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___524_238.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___524_238.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___524_238.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___524_238.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___524_238.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___524_238.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___524_238.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___524_238.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___524_238.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___524_238.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___524_238.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___524_238.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___524_238.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___524_238.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___524_238.FStar_TypeChecker_Env.dep_graph)
      } in
    let env2 =
      let uu___525_240 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___525_240.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___525_240.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___525_240.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___525_240.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___525_240.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___525_240.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___525_240.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___525_240.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___525_240.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___525_240.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___525_240.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___525_240.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___525_240.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___525_240.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___525_240.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___525_240.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___525_240.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___525_240.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___525_240.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___525_240.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___525_240.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___525_240.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___525_240.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___525_240.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___525_240.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___525_240.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___525_240.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___525_240.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___525_240.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___525_240.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___525_240.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___525_240.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___525_240.FStar_TypeChecker_Env.dep_graph)
      } in
    (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env2; env2
let tc_one_fragment:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun frag  ->
        let acceptable_mod_name modul =
          let uu____265 =
            let uu____266 =
              let uu____267 = FStar_Options.file_list () in
              FStar_List.hd uu____267 in
            FStar_Parser_Dep.lowercase_module_name uu____266 in
          let uu____270 =
            let uu____271 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
            FStar_String.lowercase uu____271 in
          uu____265 = uu____270 in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____276,{ FStar_Parser_AST.d = uu____277;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____279;
                           FStar_Parser_AST.quals = uu____280;
                           FStar_Parser_AST.attrs = uu____281;_}::uu____282)
              -> d
          | FStar_Parser_AST.Interface
              (uu____289,{ FStar_Parser_AST.d = uu____290;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____292;
                           FStar_Parser_AST.quals = uu____293;
                           FStar_Parser_AST.attrs = uu____294;_}::uu____295,uu____296)
              -> d
          | uu____303 -> FStar_Range.dummyRange in
        let uu____304 = FStar_Parser_Driver.parse_fragment frag in
        match uu____304 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____316 =
              let uu____321 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false in
              FStar_All.pipe_left (with_tcenv env) uu____321 in
            (match uu____316 with
             | (ast_modul1,env1) ->
                 let uu____342 =
                   let uu____347 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1 in
                   FStar_All.pipe_left (with_tcenv env1) uu____347 in
                 (match uu____342 with
                  | (modul,env2) ->
                      ((match curmod with
                        | FStar_Pervasives_Native.Some uu____369 when
                            let uu____370 = acceptable_mod_name modul in
                            Prims.op_Negation uu____370 ->
                            FStar_Exn.raise
                              (FStar_Errors.Error
                                 ("Interactive mode only supports a single module at the top-level",
                                   (range_of_first_mod_decl ast_modul1)))
                        | uu____371 -> ());
                       (let uu____374 =
                          let uu____383 =
                            FStar_ToSyntax_Env.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv in
                          if uu____383
                          then (modul, [], env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul
                              false in
                        match uu____374 with
                        | (modul1,uu____402,env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____419 = FStar_List.hd ast_decls in
                 (match uu____419 with
                  | { FStar_Parser_AST.d = uu____426;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____428;
                      FStar_Parser_AST.quals = uu____429;
                      FStar_Parser_AST.attrs = uu____430;_} ->
                      FStar_Exn.raise
                        (FStar_Errors.Error
                           ("First statement must be a module declaration",
                             rng)))
             | FStar_Pervasives_Native.Some modul ->
                 let uu____440 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____458 =
                            let uu____465 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl in
                            FStar_All.pipe_left (with_tcenv env1) uu____465 in
                          match uu____458 with
                          | (decls,env2) -> (env2, decls)) env ast_decls in
                 (match uu____440 with
                  | (env1,ast_decls_l) ->
                      let uu____516 =
                        let uu____521 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l) in
                        FStar_All.pipe_left (with_tcenv env1) uu____521 in
                      (match uu____516 with
                       | (sigelts,env2) ->
                           let uu____542 =
                             let uu____551 =
                               FStar_ToSyntax_Env.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv in
                             if uu____551
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts in
                           (match uu____542 with
                            | (modul1,uu____570,env3) ->
                                ((FStar_Pervasives_Native.Some modul1), env3)))))
let load_interface_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Parser_ParseIt.filename -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun interface_file_name  ->
      let r = FStar_Parser_ParseIt.parse (FStar_Util.Inl interface_file_name) in
      match r with
      | FStar_Util.Inl
          (FStar_Util.Inl (FStar_Parser_AST.Interface
           (l,decls,uu____605)),uu____606)
          ->
          let uu____651 =
            let uu____656 =
              FStar_ToSyntax_Interleave.initialize_interface l decls in
            FStar_All.pipe_left (with_tcenv env) uu____656 in
          FStar_Pervasives_Native.snd uu____651
      | FStar_Util.Inl uu____669 ->
          let uu____694 =
            let uu____695 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name in
            FStar_Errors.Err uu____695 in
          FStar_Exn.raise uu____694
      | FStar_Util.Inr (err1,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err1, rng))
let load_module_from_cache:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      (FStar_Syntax_Syntax.modul,FStar_ToSyntax_Env.module_inclusion_info)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fn  ->
      let cache_file = FStar_Parser_Dep.cache_file_name fn in
      let fail4 tag =
        (let uu____742 =
           let uu____743 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0") in
           let uu____744 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0") in
           FStar_Range.mk_range fn uu____743 uu____744 in
         let uu____745 =
           FStar_Util.format3 "%s cache file %s; will recheck %s" tag
             cache_file fn in
         FStar_Errors.warn uu____742 uu____745);
        FStar_Pervasives_Native.None in
      if FStar_Util.file_exists cache_file
      then
        let uu____756 = FStar_Util.load_value_from_file cache_file in
        match uu____756 with
        | FStar_Pervasives_Native.None  -> fail4 "Corrupt"
        | FStar_Pervasives_Native.Some (digest,tcmod,mii) ->
            let uu____804 =
              FStar_Parser_Dep.hash_dependences
                env.FStar_TypeChecker_Env.dep_graph fn in
            (match uu____804 with
             | FStar_Pervasives_Native.Some digest' when digest = digest' ->
                 FStar_Pervasives_Native.Some (tcmod, mii)
             | uu____826 -> fail4 "Stale")
      else FStar_Pervasives_Native.None
let store_module_to_cache:
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      FStar_Syntax_Syntax.modul ->
        FStar_ToSyntax_Env.module_inclusion_info -> Prims.unit
  =
  fun env  ->
    fun fn  ->
      fun modul  ->
        fun mii  ->
          let cache_file = FStar_Parser_Dep.cache_file_name fn in
          let digest =
            FStar_Parser_Dep.hash_dependences
              env.FStar_TypeChecker_Env.dep_graph fn in
          match digest with
          | FStar_Pervasives_Native.Some hashes ->
              FStar_Util.save_value_to_file cache_file (hashes, modul, mii)
          | uu____869 ->
              let uu____874 =
                let uu____875 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0") in
                let uu____876 =
                  FStar_Range.mk_pos (Prims.parse_int "0")
                    (Prims.parse_int "0") in
                FStar_Range.mk_range fn uu____875 uu____876 in
              let uu____877 =
                FStar_Util.format1
                  "%s was not written, since some of its dependences were not also checked"
                  cache_file in
              FStar_Errors.warn uu____874 uu____877
let tc_one_file:
  FStar_TypeChecker_Env.env ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2,
          FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        FStar_Syntax_Syntax.reset_gensym ();
        (let tc_source_file uu____921 =
           let uu____922 = parse env pre_fn fn in
           match uu____922 with
           | (fmod,env1) ->
               let check_mod uu____950 =
                 let uu____951 =
                   FStar_Util.record_time
                     (fun uu____965  ->
                        FStar_TypeChecker_Tc.check_module env1 fmod) in
                 match uu____951 with
                 | ((tcmod,env2),time) -> ((tcmod, time), env2) in
               let uu____985 =
                 let uu____994 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ())) in
                 if uu____994
                 then
                   let uu____1003 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1003
                     check_mod
                 else check_mod () in
               (match uu____985 with
                | (tcmod,env2) ->
                    let mii =
                      FStar_ToSyntax_Env.inclusion_info
                        env2.FStar_TypeChecker_Env.dsenv
                        (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name in
                    (tcmod, mii, env2)) in
         let uu____1038 = FStar_Options.cache_checked_modules () in
         if uu____1038
         then
           let uu____1047 = load_module_from_cache env fn in
           match uu____1047 with
           | FStar_Pervasives_Native.None  ->
               let uu____1066 = tc_source_file () in
               (match uu____1066 with
                | (tcmod,mii,env1) ->
                    ((let uu____1097 =
                        let uu____1098 = FStar_Errors.get_err_count () in
                        uu____1098 = (Prims.parse_int "0") in
                      if uu____1097
                      then
                        store_module_to_cache env1 fn
                          (FStar_Pervasives_Native.fst tcmod) mii
                      else ());
                     (tcmod, env1)))
           | FStar_Pervasives_Native.Some (tcmod,mii) ->
               let uu____1110 =
                 let uu____1115 =
                   FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii
                     (FStar_TypeChecker_Normalize.erase_universes env) in
                 FStar_All.pipe_left (with_tcenv env) uu____1115 in
               (match uu____1110 with
                | (uu____1136,env1) ->
                    let env2 =
                      FStar_TypeChecker_Tc.load_checked_module env1 tcmod in
                    ((tcmod, (Prims.parse_int "0")), env2))
         else
           (let uu____1144 = tc_source_file () in
            match uu____1144 with | (tcmod,uu____1164,env1) -> (tcmod, env1)))
let tc_prims:
  FStar_TypeChecker_Env.env ->
    ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2,
      FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    let uu____1197 = FStar_Options.prims () in
    tc_one_file env FStar_Pervasives_Native.None uu____1197
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1207 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1207 ["fsti"; "fsi"]))
        &&
        (let uu____1209 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1209 ["fst"; "fs"])
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____1217 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____1217 FStar_Pervasives.ignore);
      (let uu____1219 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____1219 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv in
      let env1 = FStar_TypeChecker_Env.push env msg in
      let uu___526_1228 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___526_1228.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___526_1228.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___526_1228.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___526_1228.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___526_1228.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___526_1228.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___526_1228.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___526_1228.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___526_1228.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___526_1228.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___526_1228.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___526_1228.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___526_1228.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___526_1228.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___526_1228.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___526_1228.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___526_1228.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___526_1228.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___526_1228.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___526_1228.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___526_1228.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___526_1228.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___526_1228.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___526_1228.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___526_1228.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___526_1228.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___526_1228.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___526_1228.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___526_1228.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___526_1228.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___526_1228.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___526_1228.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv;
        FStar_TypeChecker_Env.dep_graph =
          (uu___526_1228.FStar_TypeChecker_Env.dep_graph)
      }
let tc_one_file_from_remaining:
  Prims.string Prims.list ->
    FStar_TypeChecker_Env.env ->
      (Prims.string Prims.list,(FStar_Syntax_Syntax.modul,Prims.int)
                                 FStar_Pervasives_Native.tuple2 Prims.list,
        FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun remaining  ->
    fun env  ->
      let uu____1253 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1291 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl in
            (match uu____1291 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1356 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl in
            (match uu____1356 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env)) in
      match uu____1253 with
      | (remaining1,(nmods,env1)) -> (remaining1, nmods, env1)
let rec tc_fold_interleave:
  ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
     Prims.list,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string Prims.list ->
      ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun acc  ->
    fun remaining  ->
      match remaining with
      | [] -> acc
      | uu____1540 ->
          let uu____1543 = acc in
          (match uu____1543 with
           | (mods,env) ->
               let uu____1578 = tc_one_file_from_remaining remaining env in
               (match uu____1578 with
                | (remaining1,nmods,env1) ->
                    tc_fold_interleave ((FStar_List.append mods nmods), env1)
                      remaining1))
let batch_mode_tc:
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun filenames  ->
    fun dep_graph1  ->
      (let uu____1653 = FStar_Options.debug_any () in
       if uu____1653
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____1656 =
             let uu____1657 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file) in
             FStar_String.concat " " uu____1657 in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____1656))
       else ());
      (let env = init_env dep_graph1 in
       let uu____1666 = tc_fold_interleave ([], env) filenames in
       match uu____1666 with
       | (all_mods,env1) ->
           ((let uu____1712 =
               (FStar_Options.interactive ()) &&
                 (let uu____1714 = FStar_Errors.get_err_count () in
                  uu____1714 = (Prims.parse_int "0")) in
             if uu____1712
             then
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ()
             else
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                 ());
            (all_mods, env1)))