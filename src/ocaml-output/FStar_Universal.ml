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
            (let uu___264_61 = env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___264_61.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___264_61.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___264_61.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___264_61.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___264_61.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___264_61.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___264_61.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___264_61.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___264_61.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___264_61.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___264_61.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___264_61.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___264_61.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___264_61.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___264_61.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___264_61.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___264_61.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___264_61.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___264_61.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___264_61.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___264_61.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___264_61.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.tc_term =
                 (uu___264_61.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___264_61.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___264_61.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___264_61.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___264_61.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___264_61.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___264_61.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___264_61.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___264_61.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___264_61.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv;
               FStar_TypeChecker_Env.dep_graph =
                 (uu___264_61.FStar_TypeChecker_Env.dep_graph)
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
let init_env: FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env =
  fun deps  ->
    let solver1 =
      let uu____241 = FStar_Options.lax () in
      if uu____241
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___265_243 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___265_243.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___265_243.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___265_243.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.encode_modul =
             (uu___265_243.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___265_243.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___265_243.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.finish =
             (uu___265_243.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___265_243.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Parser_Const.prims_lid in
    let env1 =
      let uu___266_246 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___266_246.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___266_246.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___266_246.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___266_246.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___266_246.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___266_246.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___266_246.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___266_246.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___266_246.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___266_246.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___266_246.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___266_246.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___266_246.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___266_246.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___266_246.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___266_246.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___266_246.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___266_246.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___266_246.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___266_246.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___266_246.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___266_246.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___266_246.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___266_246.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___266_246.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___266_246.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___266_246.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___266_246.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___266_246.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___266_246.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___266_246.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___266_246.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___266_246.FStar_TypeChecker_Env.dep_graph)
      } in
    let env2 =
      let uu___267_248 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___267_248.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___267_248.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___267_248.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___267_248.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___267_248.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___267_248.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___267_248.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___267_248.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___267_248.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___267_248.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___267_248.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___267_248.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___267_248.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___267_248.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___267_248.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___267_248.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___267_248.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___267_248.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___267_248.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___267_248.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___267_248.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___267_248.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___267_248.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___267_248.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___267_248.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___267_248.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___267_248.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___267_248.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___267_248.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___267_248.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___267_248.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___267_248.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___267_248.FStar_TypeChecker_Env.dep_graph)
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
          let uu____276 =
            let uu____277 =
              let uu____278 = FStar_Options.file_list () in
              FStar_List.hd uu____278 in
            FStar_Parser_Dep.lowercase_module_name uu____277 in
          let uu____281 =
            let uu____282 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
            FStar_String.lowercase uu____282 in
          uu____276 = uu____281 in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu____287,{ FStar_Parser_AST.d = uu____288;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____290;
                           FStar_Parser_AST.quals = uu____291;
                           FStar_Parser_AST.attrs = uu____292;_}::uu____293)
              -> d
          | FStar_Parser_AST.Interface
              (uu____300,{ FStar_Parser_AST.d = uu____301;
                           FStar_Parser_AST.drange = d;
                           FStar_Parser_AST.doc = uu____303;
                           FStar_Parser_AST.quals = uu____304;
                           FStar_Parser_AST.attrs = uu____305;_}::uu____306,uu____307)
              -> d
          | uu____314 -> FStar_Range.dummyRange in
        let uu____315 = FStar_Parser_Driver.parse_fragment frag in
        match uu____315 with
        | FStar_Parser_Driver.Empty  -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu____327 =
              let uu____332 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false in
              FStar_All.pipe_left (with_tcenv env) uu____332 in
            (match uu____327 with
             | (ast_modul1,env1) ->
                 let uu____353 =
                   let uu____358 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1 in
                   FStar_All.pipe_left (with_tcenv env1) uu____358 in
                 (match uu____353 with
                  | (modul,env2) ->
                      ((match curmod with
                        | FStar_Pervasives_Native.Some uu____380 when
                            let uu____381 = acceptable_mod_name modul in
                            Prims.op_Negation uu____381 ->
                            FStar_Exn.raise
                              (FStar_Errors.Error
                                 ("Interactive mode only supports a single module at the top-level",
                                   (range_of_first_mod_decl ast_modul1)))
                        | uu____382 -> ());
                       (let uu____385 =
                          let uu____394 =
                            FStar_ToSyntax_Env.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv in
                          if uu____394
                          then (modul, [], env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul
                              false in
                        match uu____385 with
                        | (modul1,uu____413,env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None  ->
                 let uu____430 = FStar_List.hd ast_decls in
                 (match uu____430 with
                  | { FStar_Parser_AST.d = uu____437;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.doc = uu____439;
                      FStar_Parser_AST.quals = uu____440;
                      FStar_Parser_AST.attrs = uu____441;_} ->
                      FStar_Exn.raise
                        (FStar_Errors.Error
                           ("First statement must be a module declaration",
                             rng)))
             | FStar_Pervasives_Native.Some modul ->
                 let uu____451 =
                   FStar_Util.fold_map
                     (fun env1  ->
                        fun a_decl  ->
                          let uu____469 =
                            let uu____476 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                a_decl in
                            FStar_All.pipe_left (with_tcenv env1) uu____476 in
                          match uu____469 with
                          | (decls,env2) -> (env2, decls)) env ast_decls in
                 (match uu____451 with
                  | (env1,ast_decls_l) ->
                      let uu____527 =
                        let uu____532 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_List.flatten ast_decls_l) in
                        FStar_All.pipe_left (with_tcenv env1) uu____532 in
                      (match uu____527 with
                       | (sigelts,env2) ->
                           let uu____553 =
                             let uu____562 =
                               FStar_ToSyntax_Env.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv in
                             if uu____562
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts in
                           (match uu____553 with
                            | (modul1,uu____581,env3) ->
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
           (l,decls,uu____618)),uu____619)
          ->
          let uu____664 =
            let uu____669 =
              FStar_ToSyntax_Interleave.initialize_interface l decls in
            FStar_All.pipe_left (with_tcenv env) uu____669 in
          FStar_Pervasives_Native.snd uu____664
      | FStar_Util.Inl uu____682 ->
          let uu____707 =
            let uu____708 =
              FStar_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name in
            FStar_Errors.Err uu____708 in
          FStar_Exn.raise uu____707
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
        (let uu____757 =
           let uu____758 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0") in
           let uu____759 =
             FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0") in
           FStar_Range.mk_range fn uu____758 uu____759 in
         let uu____760 =
           FStar_Util.format3 "%s cache file %s; will recheck %s" tag
             cache_file fn in
         FStar_Errors.warn uu____757 uu____760);
        FStar_Pervasives_Native.None in
      if FStar_Util.file_exists cache_file
      then
        let uu____771 = FStar_Util.load_value_from_file cache_file in
        match uu____771 with
        | FStar_Pervasives_Native.None  -> fail4 "Corrupt"
        | FStar_Pervasives_Native.Some (digest,tcmod,mii) ->
            let uu____819 =
              FStar_Parser_Dep.hash_dependences
                env.FStar_TypeChecker_Env.dep_graph fn in
            (match uu____819 with
             | FStar_Pervasives_Native.Some digest' when digest = digest' ->
                 FStar_Pervasives_Native.Some (tcmod, mii)
             | uu____841 -> fail4 "Stale")
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
          | uu____888 -> ()
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
        (let tc_source_file uu____939 =
           let uu____940 = parse env pre_fn fn in
           match uu____940 with
           | (fmod,env1) ->
               let check_mod uu____968 =
                 let uu____969 =
                   FStar_Util.record_time
                     (fun uu____983  ->
                        FStar_TypeChecker_Tc.check_module env1 fmod) in
                 match uu____969 with
                 | ((tcmod,env2),time) -> ((tcmod, time), env2) in
               let uu____1003 =
                 let uu____1012 =
                   (FStar_Options.should_verify
                      (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ())) in
                 if uu____1012
                 then
                   let uu____1021 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1021
                     check_mod
                 else check_mod () in
               (match uu____1003 with
                | (tcmod,env2) ->
                    let mii =
                      FStar_ToSyntax_Env.inclusion_info
                        env2.FStar_TypeChecker_Env.dsenv
                        (FStar_Pervasives_Native.fst tcmod).FStar_Syntax_Syntax.name in
                    (tcmod, mii, env2)) in
         let uu____1056 = FStar_Options.cache_checked_modules () in
         if uu____1056
         then
           let uu____1065 = load_module_from_cache env fn in
           match uu____1065 with
           | FStar_Pervasives_Native.None  ->
               let uu____1084 = tc_source_file () in
               (match uu____1084 with
                | (tcmod,mii,env1) ->
                    (store_module_to_cache env1 fn
                       (FStar_Pervasives_Native.fst tcmod) mii;
                     (tcmod, env1)))
           | FStar_Pervasives_Native.Some (tcmod,mii) ->
               let uu____1125 =
                 let uu____1130 =
                   FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii in
                 FStar_All.pipe_left (with_tcenv env) uu____1130 in
               (match uu____1125 with
                | (uu____1151,env1) ->
                    let env2 =
                      FStar_TypeChecker_Tc.load_checked_module env1 tcmod in
                    ((tcmod, (Prims.parse_int "0")), env2))
         else
           (let uu____1159 = tc_source_file () in
            match uu____1159 with | (tcmod,uu____1179,env1) -> (tcmod, env1)))
let tc_prims:
  FStar_TypeChecker_Env.env ->
    ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2,
      FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    let uu____1213 = FStar_Options.prims () in
    tc_one_file env FStar_Pervasives_Native.None uu____1213
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1225 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1225 ["fsti"; "fsi"]))
        &&
        (let uu____1227 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1227 ["fst"; "fs"])
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____1237 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____1237 FStar_Pervasives.ignore);
      (let uu____1239 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____1239 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun msg  ->
      let dsenv = FStar_ToSyntax_Env.push env.FStar_TypeChecker_Env.dsenv in
      let env1 = FStar_TypeChecker_Env.push env msg in
      let uu___268_1250 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___268_1250.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___268_1250.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___268_1250.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___268_1250.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___268_1250.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___268_1250.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___268_1250.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___268_1250.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___268_1250.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___268_1250.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___268_1250.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___268_1250.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___268_1250.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___268_1250.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___268_1250.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___268_1250.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___268_1250.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___268_1250.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___268_1250.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___268_1250.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___268_1250.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___268_1250.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___268_1250.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___268_1250.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___268_1250.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___268_1250.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___268_1250.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___268_1250.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___268_1250.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___268_1250.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___268_1250.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___268_1250.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = dsenv;
        FStar_TypeChecker_Env.dep_graph =
          (uu___268_1250.FStar_TypeChecker_Env.dep_graph)
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
      let uu____1277 =
        match remaining with
        | intf::impl::remaining1 when needs_interleaving intf impl ->
            let uu____1315 =
              tc_one_file env (FStar_Pervasives_Native.Some intf) impl in
            (match uu____1315 with | (m,env1) -> (remaining1, ([m], env1)))
        | intf_or_impl::remaining1 ->
            let uu____1380 =
              tc_one_file env FStar_Pervasives_Native.None intf_or_impl in
            (match uu____1380 with | (m,env1) -> (remaining1, ([m], env1)))
        | [] -> ([], ([], env)) in
      match uu____1277 with
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
      | uu____1566 ->
          let uu____1569 = acc in
          (match uu____1569 with
           | (mods,env) ->
               let uu____1604 = tc_one_file_from_remaining remaining env in
               (match uu____1604 with
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
      (let uu____1681 = FStar_Options.debug_any () in
       if uu____1681
       then
         (FStar_Util.print_endline "Auto-deps kicked in; here's some info.";
          FStar_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu____1684 =
             let uu____1685 =
               FStar_All.pipe_right filenames
                 (FStar_List.filter FStar_Options.should_verify_file) in
             FStar_String.concat " " uu____1685 in
           FStar_Util.print1
             "Here's the list of modules we will verify: %s\n" uu____1684))
       else ());
      (let env = init_env dep_graph1 in
       let uu____1694 = tc_fold_interleave ([], env) filenames in
       match uu____1694 with
       | (all_mods,env1) ->
           ((let uu____1740 =
               (FStar_Options.interactive ()) &&
                 (let uu____1742 = FStar_Errors.get_err_count () in
                  uu____1742 = (Prims.parse_int "0")) in
             if uu____1740
             then
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                 ()
             else
               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                 ());
            (all_mods, env1)))