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
      let uu____47 = f env.FStar_TypeChecker_Env.dsenv in
      match uu____47 with
      | (a,dsenv) ->
          (a,
            (let uu___228_61 = env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___228_61.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___228_61.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___228_61.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___228_61.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___228_61.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___228_61.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___228_61.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___228_61.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___228_61.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___228_61.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___228_61.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___228_61.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___228_61.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___228_61.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___228_61.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___228_61.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___228_61.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___228_61.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___228_61.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___228_61.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___228_61.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___228_61.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.tc_term =
                 (uu___228_61.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___228_61.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___228_61.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___228_61.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___228_61.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___228_61.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___228_61.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___228_61.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___228_61.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___228_61.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv
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
        let uu____86 = FStar_Parser_Driver.parse_file fn in
        match uu____86 with
        | (ast,uu____102) ->
            let uu____115 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____125 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____125 with
                   | (pre_ast,uu____141) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____160),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____171 =
                              let uu____176 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1 in
                              FStar_All.pipe_left (with_tcenv env) uu____176 in
                            (match uu____171 with
                             | (uu____193,env1) ->
                                 let uu____195 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true in
                                 FStar_All.pipe_left (with_tcenv env1)
                                   uu____195)
                        | uu____208 ->
                            FStar_Exn.raise
                              (FStar_Errors.Err
                                 "mismatch between pre-module and module\n"))) in
            (match uu____115 with
             | (ast1,env1) ->
                 let uu____223 =
                   FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1 in
                 FStar_All.pipe_left (with_tcenv env1) uu____223)
let init_env: Prims.unit -> FStar_TypeChecker_Env.env =
  fun uu____239  ->
    let solver1 =
      let uu____241 = FStar_Options.lax () in
      if uu____241
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___229_243 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___229_243.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___229_243.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___229_243.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.encode_modul =
             (uu___229_243.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___229_243.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___229_243.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___229_243.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___229_243.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Parser_Const.prims_lid in
    let env1 =
      let uu___230_246 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___230_246.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___230_246.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___230_246.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___230_246.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___230_246.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___230_246.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___230_246.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___230_246.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___230_246.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___230_246.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___230_246.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___230_246.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___230_246.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___230_246.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___230_246.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___230_246.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___230_246.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___230_246.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___230_246.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___230_246.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___230_246.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___230_246.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___230_246.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___230_246.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___230_246.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___230_246.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___230_246.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___230_246.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___230_246.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___230_246.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___230_246.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___230_246.FStar_TypeChecker_Env.dsenv)
      } in
    let env2 =
      let uu___231_248 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___231_248.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___231_248.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___231_248.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___231_248.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___231_248.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___231_248.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___231_248.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___231_248.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___231_248.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___231_248.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___231_248.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___231_248.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___231_248.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___231_248.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___231_248.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___231_248.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___231_248.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___231_248.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___231_248.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___231_248.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___231_248.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___231_248.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___231_248.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___231_248.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___231_248.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___231_248.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___231_248.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___231_248.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___231_248.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___231_248.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___231_248.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___231_248.FStar_TypeChecker_Env.dsenv)
      } in
    (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env2; env2
let tc_prims:
  FStar_TypeChecker_Env.env ->
    ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2,
      FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    let prims_filename = FStar_Options.prims () in
    let uu____271 = parse env FStar_Pervasives_Native.None prims_filename in
    match uu____271 with
    | (prims_mod,env1) ->
        let uu____286 =
          FStar_Util.record_time
            (fun uu____300  ->
               FStar_TypeChecker_Tc.check_module env1 prims_mod) in
        (match uu____286 with
         | ((prims_mod1,env2),elapsed_time) ->
             ((prims_mod1, elapsed_time), env2))
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
          let uu____346 =
            let uu____347 =
              let uu____348 = FStar_Options.file_list () in
              FStar_List.hd uu____348 in
            FStar_Parser_Dep.lowercase_module_name uu____347 in
          let uu____351 =
            let uu____352 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
            FStar_String.lowercase uu____352 in
          uu____346 = uu____351 in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____357,{ FStar_Parser_AST.d = uu____358;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____360;
                           FStar_Parser_AST.quals = uu____361;
                           FStar_Parser_AST.attrs = uu____362;_}::uu____363)
              -> d
          | FStar_Parser_AST.Interface
              (uu____370,{ FStar_Parser_AST.d = uu____371;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____373;
                           FStar_Parser_AST.quals = uu____374;
                           FStar_Parser_AST.attrs = uu____375;_}::uu____376,uu____377)
              -> d
          | uu____384 -> FStar_Range.dummyRange in
        let uu____385 = FStar_Parser_Driver.parse_fragment frag in
        match uu____385 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____397 =
              let uu____402 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false in
              FStar_All.pipe_left (with_tcenv env) uu____402 in
            (match uu____397 with
             | (ast_modul1,env1) ->
                 let uu____423 =
                   let uu____428 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1 in
                   FStar_All.pipe_left (with_tcenv env1) uu____428 in
                 (match uu____423 with
                  | (modul,env2) ->
                      ((match curmod with
                        | FStar_Pervasives_Native.Some uu____450 when
                            let uu____451 = acceptable_mod_name modul in
                            Prims.op_Negation uu____451 ->
                            FStar_Exn.raise
                              (FStar_Errors.Error
                                 ("Interactive mode only supports a single module at the top-level",
                                   (range_of_first_mod_decl ast_modul1)))
                        | uu____452 -> ());
                       (let uu____455 =
                          let uu____464 =
                            FStar_ToSyntax_Env.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv in
                          if uu____464
                          then (modul, [], env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul
                              false in
                        match uu____455 with
                        | (modul1,uu____483,env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____500 = FStar_List.hd ast_decls in
                 (match uu____500 with
                  | { FStar_Parser_AST.d = uu____507;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____509;
                      FStar_Parser_AST.quals = uu____510;
                      FStar_Parser_AST.attrs = uu____511;_} ->
                      FStar_Exn.raise
                        (FStar_Errors.Error
                           ("First statement must be a module declaration",
                             rng)))
             | FStar_Pervasives_Native.Some modul ->
                 let uu____521 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____539 =
                            let uu____546 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl in
                            FStar_All.pipe_left (with_tcenv env1) uu____546 in
                          match uu____539 with
                          | (decls,env2) -> (env2, decls)) env ast_decls in
                 (match uu____521 with
                  | (env1,ast_decls_l) ->
                      let uu____597 =
                        let uu____602 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l) in
                        FStar_All.pipe_left (with_tcenv env1) uu____602 in
                      (match uu____597 with
                       | (sigelts,env2) ->
                           let uu____623 =
                             let uu____632 =
                               FStar_ToSyntax_Env.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv in
                             if uu____632
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts in
                           (match uu____623 with
                            | (modul1,uu____651,env3) ->
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
           (l,decls,uu____688)),uu____689)
          ->
          let uu____734 =
            let uu____739 =
              FStar_ToSyntax_Interleave.initialize_interface l decls in
            FStar_All.pipe_left (with_tcenv env) uu____739 in
          FStar_Pervasives_Native.snd uu____734
      | FStar_Util.Inl uu____752 ->
          let uu____777 =
            let uu____778 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name in
            FStar_Errors.Err uu____778 in
          FStar_Exn.raise uu____777
      | FStar_Util.Inr (err1,rng) ->
          FStar_Exn.raise (FStar_Errors.Error (err1, rng))
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
        let checked_file_name =
          let uu____828 = FStar_Parser_ParseIt.find_file fn in
          Prims.strcat uu____828 ".checked" in
        let lax_checked_file_name = Prims.strcat checked_file_name ".lax" in
        let lax_ok =
          let uu____831 = FStar_Options.should_verify_file fn in
          Prims.op_Negation uu____831 in
        let cache_file_to_write =
          if lax_ok then lax_checked_file_name else checked_file_name in
        let cache_file_to_read uu____839 =
          if FStar_Util.file_exists checked_file_name
          then FStar_Pervasives_Native.Some checked_file_name
          else
            if lax_ok && (FStar_Util.file_exists lax_checked_file_name)
            then FStar_Pervasives_Native.Some lax_checked_file_name
            else FStar_Pervasives_Native.None in
        let tc_source_file uu____857 =
          let uu____858 = parse env pre_fn fn in
          match uu____858 with
          | (fmod,env1) ->
              let check_mod uu____884 =
                let uu____885 =
                  FStar_Util.record_time
                    (fun uu____899  ->
                       FStar_TypeChecker_Tc.check_module env1 fmod) in
                match uu____885 with
                | ((tcmod,env2),time) -> ((tcmod, time), env2) in
              let uu____919 =
                let uu____928 =
                  (FStar_Options.should_verify
                     (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                    &&
                    ((FStar_Options.record_hints ()) ||
                       (FStar_Options.use_hints ())) in
                if uu____928
                then
                  let uu____937 = FStar_Parser_ParseIt.find_file fn in
                  FStar_SMTEncoding_Solver.with_hints_db uu____937 check_mod
                else check_mod () in
              (match uu____919 with
               | (tcmod,env2) ->
                   ((let uu____966 = FStar_Options.cache_checked_modules () in
                     if uu____966
                     then
                       let uu____967 = tcmod in
                       match uu____967 with
                       | (tcmod1,uu____973) ->
                           let mii =
                             FStar_ToSyntax_Env.inclusion_info
                               env2.FStar_TypeChecker_Env.dsenv
                               tcmod1.FStar_Syntax_Syntax.name in
                           let uu____975 =
                             let uu____982 = FStar_Util.digest_of_file fn in
                             (uu____982, tcmod1, mii) in
                           FStar_Util.save_value_to_file cache_file_to_write
                             uu____975
                     else ());
                    (tcmod, env2))) in
        let uu____994 = FStar_Options.cache_checked_modules () in
        if uu____994
        then
          match cache_file_to_read () with
          | FStar_Pervasives_Native.None  -> tc_source_file ()
          | FStar_Pervasives_Native.Some cache_file ->
              let uu____1012 = FStar_Util.load_value_from_file cache_file in
              (match uu____1012 with
               | FStar_Pervasives_Native.None  ->
                   failwith (Prims.strcat "Corrupt file: " cache_file)
               | FStar_Pervasives_Native.Some (digest,tcmod,mii) ->
                   let uu____1058 =
                     let uu____1059 = FStar_Util.digest_of_file fn in
                     digest = uu____1059 in
                   if uu____1058
                   then
                     let uu____1068 =
                       let uu____1073 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii in
                       FStar_All.pipe_left (with_tcenv env) uu____1073 in
                     (match uu____1068 with
                      | (uu____1094,env1) ->
                          let env2 =
                            FStar_TypeChecker_Tc.load_checked_module env1
                              tcmod in
                          ((tcmod, (Prims.parse_int "0")), env2))
                   else
                     (let uu____1102 =
                        FStar_Util.format1 "The file %s is stale; delete it"
                          cache_file in
                      failwith uu____1102))
        else tc_source_file ()
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1123 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1123 ["fsti"; "fsi"]))
        &&
        (let uu____1125 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1125 ["fst"; "fs"])
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____1135 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____1135 FStar_Pervasives.ignore);
      (let uu____1137 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____1137 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv in
      let env1 = FStar_TypeChecker_Env.push env msg in
      let uu___232_1148 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___232_1148.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___232_1148.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___232_1148.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___232_1148.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___232_1148.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___232_1148.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___232_1148.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___232_1148.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___232_1148.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___232_1148.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___232_1148.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___232_1148.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___232_1148.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___232_1148.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___232_1148.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___232_1148.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___232_1148.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___232_1148.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___232_1148.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___232_1148.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___232_1148.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___232_1148.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___232_1148.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___232_1148.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___232_1148.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___232_1148.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___232_1148.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___232_1148.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___232_1148.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___232_1148.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___232_1148.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___232_1148.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv
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
      let uu____1175 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1213 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl in
            (match uu____1213 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1278 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl in
            (match uu____1278 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env)) in
      match uu____1175 with
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
      | uu____1464 ->
          let uu____1467 = acc in
          (match uu____1467 with
           | (mods,env) ->
               let uu____1502 = tc_one_file_from_remaining remaining env in
               (match uu____1502 with
                | (remaining1,nmods,env1) ->
                    tc_fold_interleave ((FStar_List.append mods nmods), env1)
                      remaining1))
let batch_mode_tc_no_prims:
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
         Prims.list,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun filenames  ->
      let uu____1578 = tc_fold_interleave ([], env) filenames in
      match uu____1578 with
      | (all_mods,env1) ->
          ((let uu____1624 =
              (FStar_Options.interactive ()) &&
                (let uu____1626 = FStar_Errors.get_err_count () in
                 uu____1626 = (Prims.parse_int "0")) in
            if uu____1624
            then
              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                ()
            else
              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                ());
           (all_mods, env1))
let batch_mode_tc:
  Prims.string Prims.list ->
    ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
       Prims.list,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple2
  =
  fun filenames  ->
    let uu____1652 = let uu____1661 = init_env () in tc_prims uu____1661 in
    match uu____1652 with
    | (prims_mod,env) ->
        ((let uu____1683 =
            (let uu____1686 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1686) && (FStar_Options.debug_any ()) in
          if uu____1683
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1689 =
                let uu____1690 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1690 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1689))
          else ());
         (let uu____1694 = batch_mode_tc_no_prims env filenames in
          match uu____1694 with
          | (all_mods,env1) -> ((prims_mod :: all_mods), env1)))