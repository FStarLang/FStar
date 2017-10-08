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
      (FStar_Parser_ParseIt.input_frag,Prims.bool)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun uu____343  ->
        match uu____343 with
        | (frag,is_interface_dependence) ->
            let uu____358 = FStar_Parser_Driver.parse_fragment frag in
            (match uu____358 with
             | FStar_Parser_Driver.Empty  -> (curmod, env)
             | FStar_Parser_Driver.Modul ast_modul ->
                 let uu____368 =
                   let uu____373 =
                     FStar_ToSyntax_Interleave.interleave_module ast_modul
                       false in
                   FStar_All.pipe_left (with_tcenv env) uu____373 in
                 (match uu____368 with
                  | (ast_modul1,env1) ->
                      let uu____394 =
                        let uu____399 =
                          FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                            curmod ast_modul1 in
                        FStar_All.pipe_left (with_tcenv env1) uu____399 in
                      (match uu____394 with
                       | (modul,env2) ->
                           let env3 =
                             if is_interface_dependence
                             then
                               let uu___232_421 = env2 in
                               let uu____422 =
                                 FStar_ToSyntax_Env.set_iface
                                   env2.FStar_TypeChecker_Env.dsenv false in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___232_421.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___232_421.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___232_421.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___232_421.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___232_421.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___232_421.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___232_421.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___232_421.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___232_421.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___232_421.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___232_421.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___232_421.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___232_421.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___232_421.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___232_421.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___232_421.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___232_421.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___232_421.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___232_421.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___232_421.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___232_421.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___232_421.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___232_421.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___232_421.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___232_421.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___232_421.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___232_421.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___232_421.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___232_421.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___232_421.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___232_421.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___232_421.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv = uu____422
                               }
                             else env2 in
                           let env4 =
                             match curmod with
                             | FStar_Pervasives_Native.Some modul1 ->
                                 let uu____426 =
                                   let uu____427 =
                                     let uu____428 =
                                       let uu____429 =
                                         FStar_Options.file_list () in
                                       FStar_List.hd uu____429 in
                                     FStar_Parser_Dep.lowercase_module_name
                                       uu____428 in
                                   let uu____432 =
                                     let uu____433 =
                                       FStar_Ident.string_of_lid
                                         modul1.FStar_Syntax_Syntax.name in
                                     FStar_String.lowercase uu____433 in
                                   uu____427 <> uu____432 in
                                 if uu____426
                                 then
                                   FStar_Exn.raise
                                     (FStar_Errors.Err
                                        "Interactive mode only supports a single module at the top-level")
                                 else env3
                             | FStar_Pervasives_Native.None  -> env3 in
                           let uu____435 =
                             let uu____444 =
                               FStar_ToSyntax_Env.syntax_only
                                 env4.FStar_TypeChecker_Env.dsenv in
                             if uu____444
                             then (modul, [], env4)
                             else
                               FStar_TypeChecker_Tc.tc_partial_modul env4
                                 modul false in
                           (match uu____435 with
                            | (modul1,uu____463,env5) ->
                                ((FStar_Pervasives_Native.Some modul1), env5))))
             | FStar_Parser_Driver.Decls ast_decls ->
                 let uu____474 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____492 =
                            let uu____499 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl in
                            FStar_All.pipe_left (with_tcenv env1) uu____499 in
                          match uu____492 with
                          | (decls,env2) -> (env2, decls)) env ast_decls in
                 (match uu____474 with
                  | (env1,ast_decls_l) ->
                      let uu____550 =
                        let uu____555 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l) in
                        FStar_All.pipe_left (with_tcenv env1) uu____555 in
                      (match uu____550 with
                       | (sigelts,env2) ->
                           (match curmod with
                            | FStar_Pervasives_Native.None  ->
                                (FStar_Util.print_error
                                   "fragment without an enclosing module";
                                 FStar_All.exit (Prims.parse_int "1"))
                            | FStar_Pervasives_Native.Some modul ->
                                let uu____590 =
                                  let uu____599 =
                                    FStar_ToSyntax_Env.syntax_only
                                      env2.FStar_TypeChecker_Env.dsenv in
                                  if uu____599
                                  then (modul, [], env2)
                                  else
                                    FStar_TypeChecker_Tc.tc_more_partial_modul
                                      env2 modul sigelts in
                                (match uu____590 with
                                 | (modul1,uu____618,env3) ->
                                     ((FStar_Pervasives_Native.Some modul1),
                                       env3))))))
let load_interface_decls:
  FStar_TypeChecker_Env.env ->
    FStar_Parser_ParseIt.filename -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun interface_file_name  ->
      try
        let r =
          FStar_Parser_ParseIt.parse (FStar_Util.Inl interface_file_name) in
        match r with
        | FStar_Util.Inl
            (FStar_Util.Inl (FStar_Parser_AST.Interface
             (l,decls,uu____663)),uu____664)
            ->
            let uu____709 =
              let uu____714 =
                FStar_ToSyntax_Interleave.initialize_interface l decls in
              FStar_All.pipe_left (with_tcenv env) uu____714 in
            FStar_Pervasives_Native.snd uu____709
        | FStar_Util.Inl uu____727 ->
            let uu____752 =
              let uu____753 =
                FStar_Util.format1
                  "Unexpected result from parsing %s; expected a single interface"
                  interface_file_name in
              FStar_Errors.Err uu____753 in
            FStar_Exn.raise uu____752
        | FStar_Util.Inr (err1,rng) ->
            FStar_Exn.raise (FStar_Errors.Error (err1, rng))
      with
      | FStar_Errors.Error (msg,r) when
          let uu____777 = FStar_Options.trace_error () in
          Prims.op_Negation uu____777 ->
          (FStar_TypeChecker_Err.add_errors env [(msg, r)]; env)
      | FStar_Errors.Err msg when
          let uu____788 = FStar_Options.trace_error () in
          Prims.op_Negation uu____788 ->
          (FStar_TypeChecker_Err.add_errors env
             [(msg, FStar_Range.dummyRange)];
           env)
      | e when
          let uu____799 = FStar_Options.trace_error () in
          Prims.op_Negation uu____799 -> FStar_Exn.raise e
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
          let uu____833 = FStar_Parser_ParseIt.find_file fn in
          Prims.strcat uu____833 ".checked" in
        let lax_checked_file_name = Prims.strcat checked_file_name ".lax" in
        let lax_ok =
          let uu____836 = FStar_Options.should_verify_file fn in
          Prims.op_Negation uu____836 in
        let cache_file_to_write =
          if lax_ok then lax_checked_file_name else checked_file_name in
        let cache_file_to_read uu____844 =
          if FStar_Util.file_exists checked_file_name
          then FStar_Pervasives_Native.Some checked_file_name
          else
            if lax_ok && (FStar_Util.file_exists lax_checked_file_name)
            then FStar_Pervasives_Native.Some lax_checked_file_name
            else FStar_Pervasives_Native.None in
        let tc_source_file uu____862 =
          let uu____863 = parse env pre_fn fn in
          match uu____863 with
          | (fmod,env1) ->
              let check_mod uu____889 =
                let uu____890 =
                  FStar_Util.record_time
                    (fun uu____904  ->
                       FStar_TypeChecker_Tc.check_module env1 fmod) in
                match uu____890 with
                | ((tcmod,env2),time) -> ((tcmod, time), env2) in
              let uu____924 =
                let uu____933 =
                  (FStar_Options.should_verify
                     (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                    &&
                    ((FStar_Options.record_hints ()) ||
                       (FStar_Options.use_hints ())) in
                if uu____933
                then
                  let uu____942 = FStar_Parser_ParseIt.find_file fn in
                  FStar_SMTEncoding_Solver.with_hints_db uu____942 check_mod
                else check_mod () in
              (match uu____924 with
               | (tcmod,env2) ->
                   ((let uu____971 = FStar_Options.cache_checked_modules () in
                     if uu____971
                     then
                       let uu____972 = tcmod in
                       match uu____972 with
                       | (tcmod1,uu____978) ->
                           let mii =
                             FStar_ToSyntax_Env.inclusion_info
                               env2.FStar_TypeChecker_Env.dsenv
                               tcmod1.FStar_Syntax_Syntax.name in
                           let uu____980 =
                             let uu____987 = FStar_Util.digest_of_file fn in
                             (uu____987, tcmod1, mii) in
                           FStar_Util.save_value_to_file cache_file_to_write
                             uu____980
                     else ());
                    (tcmod, env2))) in
        let uu____999 = FStar_Options.cache_checked_modules () in
        if uu____999
        then
          match cache_file_to_read () with
          | FStar_Pervasives_Native.None  -> tc_source_file ()
          | FStar_Pervasives_Native.Some cache_file ->
              let uu____1017 = FStar_Util.load_value_from_file cache_file in
              (match uu____1017 with
               | FStar_Pervasives_Native.None  ->
                   failwith (Prims.strcat "Corrupt file: " cache_file)
               | FStar_Pervasives_Native.Some (digest,tcmod,mii) ->
                   let uu____1063 =
                     let uu____1064 = FStar_Util.digest_of_file fn in
                     digest = uu____1064 in
                   if uu____1063
                   then
                     let uu____1073 =
                       let uu____1078 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii in
                       FStar_All.pipe_left (with_tcenv env) uu____1078 in
                     (match uu____1073 with
                      | (uu____1099,env1) ->
                          let env2 =
                            FStar_TypeChecker_Tc.load_checked_module env1
                              tcmod in
                          ((tcmod, (Prims.parse_int "0")), env2))
                   else
                     (let uu____1107 =
                        FStar_Util.format1 "The file %s is stale; delete it"
                          cache_file in
                      failwith uu____1107))
        else tc_source_file ()
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1128 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1128 ["fsti"; "fsi"]))
        &&
        (let uu____1130 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1130 ["fst"; "fs"])
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____1140 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____1140 FStar_Pervasives.ignore);
      (let uu____1142 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____1142 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv in
      let env1 = FStar_TypeChecker_Env.push env msg in
      let uu___235_1153 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___235_1153.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___235_1153.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___235_1153.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___235_1153.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___235_1153.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___235_1153.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___235_1153.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___235_1153.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___235_1153.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___235_1153.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___235_1153.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___235_1153.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___235_1153.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___235_1153.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___235_1153.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___235_1153.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___235_1153.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___235_1153.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___235_1153.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___235_1153.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___235_1153.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___235_1153.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___235_1153.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___235_1153.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___235_1153.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___235_1153.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___235_1153.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___235_1153.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___235_1153.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___235_1153.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___235_1153.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___235_1153.FStar_TypeChecker_Env.tc_hooks);
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
      let uu____1180 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1218 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl in
            (match uu____1218 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1283 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl in
            (match uu____1283 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env)) in
      match uu____1180 with
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
      | uu____1469 ->
          let uu____1472 = acc in
          (match uu____1472 with
           | (mods,env) ->
               let uu____1507 = tc_one_file_from_remaining remaining env in
               (match uu____1507 with
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
      let uu____1583 = tc_fold_interleave ([], env) filenames in
      match uu____1583 with
      | (all_mods,env1) ->
          ((let uu____1629 =
              (FStar_Options.interactive ()) &&
                (let uu____1631 = FStar_Errors.get_err_count () in
                 uu____1631 = (Prims.parse_int "0")) in
            if uu____1629
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
    let uu____1657 = let uu____1666 = init_env () in tc_prims uu____1666 in
    match uu____1657 with
    | (prims_mod,env) ->
        ((let uu____1688 =
            (let uu____1691 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1691) && (FStar_Options.debug_any ()) in
          if uu____1688
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1694 =
                let uu____1695 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1695 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1694))
          else ());
         (let uu____1699 = batch_mode_tc_no_prims env filenames in
          match uu____1699 with
          | (all_mods,env1) -> ((prims_mod :: all_mods), env1)))