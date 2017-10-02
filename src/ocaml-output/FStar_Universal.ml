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
            (let uu___227_61 = env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___227_61.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___227_61.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___227_61.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___227_61.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___227_61.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___227_61.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___227_61.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___227_61.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___227_61.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___227_61.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___227_61.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___227_61.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___227_61.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___227_61.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___227_61.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___227_61.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___227_61.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___227_61.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___227_61.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___227_61.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___227_61.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___227_61.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.tc_term =
                 (uu___227_61.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___227_61.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___227_61.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___227_61.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___227_61.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___227_61.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___227_61.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___227_61.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___227_61.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___227_61.FStar_TypeChecker_Env.tc_hooks);
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
        (let uu___228_243 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___228_243.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___228_243.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___228_243.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.encode_modul =
             (uu___228_243.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___228_243.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___228_243.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___228_243.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___228_243.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___228_243.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Parser_Const.prims_lid in
    let env1 =
      let uu___229_246 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___229_246.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___229_246.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___229_246.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___229_246.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___229_246.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___229_246.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___229_246.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___229_246.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___229_246.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___229_246.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___229_246.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___229_246.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___229_246.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___229_246.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___229_246.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___229_246.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___229_246.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___229_246.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___229_246.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___229_246.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___229_246.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___229_246.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___229_246.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___229_246.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___229_246.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___229_246.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___229_246.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___229_246.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___229_246.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___229_246.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___229_246.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___229_246.FStar_TypeChecker_Env.dsenv)
      } in
    let env2 =
      let uu___230_248 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___230_248.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___230_248.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___230_248.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___230_248.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___230_248.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___230_248.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___230_248.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___230_248.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___230_248.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___230_248.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___230_248.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___230_248.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___230_248.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___230_248.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___230_248.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___230_248.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___230_248.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___230_248.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___230_248.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___230_248.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___230_248.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___230_248.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___230_248.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___230_248.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___230_248.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___230_248.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___230_248.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___230_248.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___230_248.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___230_248.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___230_248.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___230_248.FStar_TypeChecker_Env.dsenv)
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
          FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun curmod  ->
    fun env  ->
      fun uu____345  ->
        match uu____345 with
        | (frag,is_interface_dependence) ->
            (try
               let uu____381 = FStar_Parser_Driver.parse_fragment frag in
               match uu____381 with
               | FStar_Parser_Driver.Empty  ->
                   FStar_Pervasives_Native.Some (curmod, env)
               | FStar_Parser_Driver.Modul ast_modul ->
                   let uu____399 =
                     let uu____404 =
                       FStar_ToSyntax_Interleave.interleave_module ast_modul
                         false in
                     FStar_All.pipe_left (with_tcenv env) uu____404 in
                   (match uu____399 with
                    | (ast_modul1,env1) ->
                        let uu____427 =
                          let uu____432 =
                            FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                              curmod ast_modul1 in
                          FStar_All.pipe_left (with_tcenv env1) uu____432 in
                        (match uu____427 with
                         | (modul,env2) ->
                             let env3 =
                               if is_interface_dependence
                               then
                                 let uu___233_456 = env2 in
                                 let uu____457 =
                                   FStar_ToSyntax_Env.set_iface
                                     env2.FStar_TypeChecker_Env.dsenv false in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___233_456.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___233_456.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___233_456.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___233_456.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___233_456.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___233_456.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___233_456.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___233_456.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___233_456.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___233_456.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___233_456.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___233_456.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___233_456.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___233_456.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___233_456.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___233_456.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___233_456.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___233_456.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___233_456.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___233_456.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___233_456.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___233_456.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___233_456.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___233_456.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___233_456.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___233_456.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___233_456.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___233_456.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___233_456.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___233_456.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___233_456.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___233_456.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv = uu____457
                                 }
                               else env2 in
                             let env4 =
                               match curmod with
                               | FStar_Pervasives_Native.Some modul1 ->
                                   let uu____461 =
                                     let uu____462 =
                                       let uu____463 =
                                         let uu____464 =
                                           FStar_Options.file_list () in
                                         FStar_List.hd uu____464 in
                                       FStar_Parser_Dep.lowercase_module_name
                                         uu____463 in
                                     let uu____467 =
                                       let uu____468 =
                                         FStar_Ident.string_of_lid
                                           modul1.FStar_Syntax_Syntax.name in
                                       FStar_String.lowercase uu____468 in
                                     uu____462 <> uu____467 in
                                   if uu____461
                                   then
                                     FStar_Exn.raise
                                       (FStar_Errors.Err
                                          "Interactive mode only supports a single module at the top-level")
                                   else env3
                               | FStar_Pervasives_Native.None  -> env3 in
                             let uu____470 =
                               let uu____479 =
                                 FStar_ToSyntax_Env.syntax_only
                                   env4.FStar_TypeChecker_Env.dsenv in
                               if uu____479
                               then (modul, [], env4)
                               else
                                 FStar_TypeChecker_Tc.tc_partial_modul env4
                                   modul in
                             (match uu____470 with
                              | (modul1,uu____500,env5) ->
                                  FStar_Pervasives_Native.Some
                                    ((FStar_Pervasives_Native.Some modul1),
                                      env5))))
               | FStar_Parser_Driver.Decls ast_decls ->
                   let uu____517 =
                     FStar_Util.fold_map
                       (fun env1  ->
                          fun a_decl  ->
                            let uu____535 =
                              let uu____542 =
                                FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                  a_decl in
                              FStar_All.pipe_left (with_tcenv env1) uu____542 in
                            match uu____535 with
                            | (decls,env2) -> (env2, decls)) env ast_decls in
                   (match uu____517 with
                    | (env1,ast_decls_l) ->
                        let uu____595 =
                          let uu____600 =
                            FStar_ToSyntax_ToSyntax.decls_to_sigelts
                              (FStar_List.flatten ast_decls_l) in
                          FStar_All.pipe_left (with_tcenv env1) uu____600 in
                        (match uu____595 with
                         | (sigelts,env2) ->
                             (match curmod with
                              | FStar_Pervasives_Native.None  ->
                                  (FStar_Util.print_error
                                     "fragment without an enclosing module";
                                   FStar_All.exit (Prims.parse_int "1"))
                              | FStar_Pervasives_Native.Some modul ->
                                  let uu____641 =
                                    let uu____650 =
                                      FStar_ToSyntax_Env.syntax_only
                                        env2.FStar_TypeChecker_Env.dsenv in
                                    if uu____650
                                    then (modul, [], env2)
                                    else
                                      FStar_TypeChecker_Tc.tc_more_partial_modul
                                        env2 modul sigelts in
                                  (match uu____641 with
                                   | (modul1,uu____671,env3) ->
                                       FStar_Pervasives_Native.Some
                                         ((FStar_Pervasives_Native.Some
                                             modul1), env3)))))
             with
             | FStar_Errors.Error (msg,r) when
                 let uu____700 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____700 ->
                 (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                  FStar_Pervasives_Native.None)
             | FStar_Errors.Err msg when
                 let uu____717 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____717 ->
                 (FStar_TypeChecker_Err.add_errors env
                    [(msg, FStar_Range.dummyRange)];
                  FStar_Pervasives_Native.None)
             | e when
                 let uu____734 = FStar_Options.trace_error () in
                 Prims.op_Negation uu____734 -> FStar_Exn.raise e)
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
             (l,decls,uu____780)),uu____781)
            ->
            let uu____826 =
              let uu____831 =
                FStar_ToSyntax_Interleave.initialize_interface l decls in
              FStar_All.pipe_left (with_tcenv env) uu____831 in
            FStar_Pervasives_Native.snd uu____826
        | FStar_Util.Inl uu____844 ->
            let uu____869 =
              let uu____870 =
                FStar_Util.format1
                  "Unexpected result from parsing %s; expected a single interface"
                  interface_file_name in
              FStar_Errors.Err uu____870 in
            FStar_Exn.raise uu____869
        | FStar_Util.Inr (err1,rng) ->
            FStar_Exn.raise (FStar_Errors.Error (err1, rng))
      with
      | FStar_Errors.Error (msg,r) when
          let uu____894 = FStar_Options.trace_error () in
          Prims.op_Negation uu____894 ->
          (FStar_TypeChecker_Err.add_errors env [(msg, r)]; env)
      | FStar_Errors.Err msg when
          let uu____905 = FStar_Options.trace_error () in
          Prims.op_Negation uu____905 ->
          (FStar_TypeChecker_Err.add_errors env
             [(msg, FStar_Range.dummyRange)];
           env)
      | e when
          let uu____916 = FStar_Options.trace_error () in
          Prims.op_Negation uu____916 -> FStar_Exn.raise e
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
          let uu____950 = FStar_Parser_ParseIt.find_file fn in
          Prims.strcat uu____950 ".checked" in
        let lax_checked_file_name = Prims.strcat checked_file_name ".lax" in
        let lax_ok =
          let uu____953 = FStar_Options.should_verify_file fn in
          Prims.op_Negation uu____953 in
        let cache_file_to_write =
          if lax_ok then lax_checked_file_name else checked_file_name in
        let cache_file_to_read uu____961 =
          if FStar_Util.file_exists checked_file_name
          then FStar_Pervasives_Native.Some checked_file_name
          else
            if lax_ok && (FStar_Util.file_exists lax_checked_file_name)
            then FStar_Pervasives_Native.Some lax_checked_file_name
            else FStar_Pervasives_Native.None in
        let tc_source_file uu____979 =
          let uu____980 = parse env pre_fn fn in
          match uu____980 with
          | (fmod,env1) ->
              let check_mod uu____1006 =
                let uu____1007 =
                  FStar_Util.record_time
                    (fun uu____1021  ->
                       FStar_TypeChecker_Tc.check_module env1 fmod) in
                match uu____1007 with
                | ((tcmod,env2),time) -> ((tcmod, time), env2) in
              let uu____1041 =
                let uu____1050 =
                  (FStar_Options.should_verify
                     (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                    &&
                    ((FStar_Options.record_hints ()) ||
                       (FStar_Options.use_hints ())) in
                if uu____1050
                then
                  let uu____1059 = FStar_Parser_ParseIt.find_file fn in
                  FStar_SMTEncoding_Solver.with_hints_db uu____1059 check_mod
                else check_mod () in
              (match uu____1041 with
               | (tcmod,env2) ->
                   ((let uu____1088 = FStar_Options.cache_checked_modules () in
                     if uu____1088
                     then
                       let uu____1089 = tcmod in
                       match uu____1089 with
                       | (tcmod1,uu____1095) ->
                           let mii =
                             FStar_ToSyntax_Env.inclusion_info
                               env2.FStar_TypeChecker_Env.dsenv
                               tcmod1.FStar_Syntax_Syntax.name in
                           let uu____1097 =
                             let uu____1104 = FStar_Util.digest_of_file fn in
                             (uu____1104, tcmod1, mii) in
                           FStar_Util.save_value_to_file cache_file_to_write
                             uu____1097
                     else ());
                    (tcmod, env2))) in
        let uu____1116 = FStar_Options.cache_checked_modules () in
        if uu____1116
        then
          match cache_file_to_read () with
          | FStar_Pervasives_Native.None  -> tc_source_file ()
          | FStar_Pervasives_Native.Some cache_file ->
              let uu____1134 = FStar_Util.load_value_from_file cache_file in
              (match uu____1134 with
               | FStar_Pervasives_Native.None  ->
                   failwith (Prims.strcat "Corrupt file: " cache_file)
               | FStar_Pervasives_Native.Some (digest,tcmod,mii) ->
                   let uu____1180 =
                     let uu____1181 = FStar_Util.digest_of_file fn in
                     digest = uu____1181 in
                   if uu____1180
                   then
                     let uu____1190 =
                       let uu____1195 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii in
                       FStar_All.pipe_left (with_tcenv env) uu____1195 in
                     (match uu____1190 with
                      | (uu____1216,env1) ->
                          let env2 =
                            FStar_TypeChecker_Tc.load_checked_module env1
                              tcmod in
                          ((tcmod, (Prims.parse_int "0")), env2))
                   else
                     (let uu____1224 =
                        FStar_Util.format1 "The file %s is stale; delete it"
                          cache_file in
                      failwith uu____1224))
        else tc_source_file ()
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1245 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1245 ["fsti"; "fsi"]))
        &&
        (let uu____1247 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1247 ["fst"; "fs"])
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____1257 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____1257 FStar_Pervasives.ignore);
      (let uu____1259 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____1259 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv in
      let env1 = FStar_TypeChecker_Env.push env msg in
      let uu___236_1270 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___236_1270.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___236_1270.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___236_1270.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___236_1270.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___236_1270.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___236_1270.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___236_1270.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___236_1270.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___236_1270.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___236_1270.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___236_1270.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___236_1270.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___236_1270.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___236_1270.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___236_1270.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___236_1270.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___236_1270.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___236_1270.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___236_1270.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___236_1270.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___236_1270.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___236_1270.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___236_1270.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___236_1270.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___236_1270.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___236_1270.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___236_1270.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___236_1270.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___236_1270.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___236_1270.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___236_1270.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___236_1270.FStar_TypeChecker_Env.tc_hooks);
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
      let uu____1297 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1335 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl in
            (match uu____1335 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1400 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl in
            (match uu____1400 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env)) in
      match uu____1297 with
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
      | uu____1586 ->
          let uu____1589 = acc in
          (match uu____1589 with
           | (mods,env) ->
               let uu____1624 = tc_one_file_from_remaining remaining env in
               (match uu____1624 with
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
      let uu____1700 = tc_fold_interleave ([], env) filenames in
      match uu____1700 with
      | (all_mods,env1) ->
          ((let uu____1746 =
              (FStar_Options.interactive ()) &&
                (let uu____1748 = FStar_Errors.get_err_count () in
                 uu____1748 = (Prims.parse_int "0")) in
            if uu____1746
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
    let uu____1774 = let uu____1783 = init_env () in tc_prims uu____1783 in
    match uu____1774 with
    | (prims_mod,env) ->
        ((let uu____1805 =
            (let uu____1808 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1808) && (FStar_Options.debug_any ()) in
          if uu____1805
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1811 =
                let uu____1812 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1812 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1811))
          else ());
         (let uu____1816 = batch_mode_tc_no_prims env filenames in
          match uu____1816 with
          | (all_mods,env1) -> ((prims_mod :: all_mods), env1)))