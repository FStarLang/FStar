open Prims
let module_or_interface_name:
  FStar_Syntax_Syntax.modul ->
    (Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2
  =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
let user_tactics_modules: Prims.string Prims.list FStar_ST.ref =
  FStar_TypeChecker_Tc.user_tactics_modules
let parse:
  FStar_ToSyntax_Env.env ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____48 = FStar_Parser_Driver.parse_file fn in
        match uu____48 with
        | (ast,uu____66) ->
            let uu____79 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (env, ast)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____89 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____89 with
                   | (pre_ast,uu____105) ->
                       (match (pre_ast, ast) with
                        | ((FStar_Parser_AST.Interface
                           (lid1,decls1,uu____124))::[],(FStar_Parser_AST.Module
                           (lid2,decls2))::[]) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let env1 =
                              FStar_ToSyntax_Interleave.initialize_interface
                                lid1 decls1 env in
                            let uu____140 =
                              let uu____145 = FStar_List.hd ast in
                              FStar_ToSyntax_Interleave.interleave_module
                                env1 uu____145 true in
                            (match uu____140 with
                             | (env2,ast1) -> (env2, [ast1]))
                        | uu____154 ->
                            FStar_Exn.raise
                              (FStar_Errors.Err
                                 "mismatch between pre-module and module\n"))) in
            (match uu____79 with
             | (env1,ast1) -> FStar_ToSyntax_ToSyntax.desugar_file env1 ast1)
let tc_prims:
  Prims.unit ->
    ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2,
      FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple3
  =
  fun uu____184  ->
    let solver1 =
      let uu____196 = FStar_Options.lax () in
      if uu____196
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___188_198 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___188_198.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___188_198.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___188_198.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___188_198.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___188_198.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___188_198.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___188_198.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___188_198.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___188_198.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___188_198.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___188_198.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___188_198.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Parser_Const.prims_lid in
    let env1 =
      let uu___189_201 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___189_201.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___189_201.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___189_201.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___189_201.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___189_201.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___189_201.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___189_201.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___189_201.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___189_201.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___189_201.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___189_201.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___189_201.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___189_201.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___189_201.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___189_201.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___189_201.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___189_201.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___189_201.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___189_201.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___189_201.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___189_201.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.type_of =
          (uu___189_201.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___189_201.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___189_201.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___189_201.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___189_201.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___189_201.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___189_201.FStar_TypeChecker_Env.identifier_info)
      } in
    let env2 =
      let uu___190_203 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___190_203.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___190_203.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___190_203.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___190_203.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___190_203.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___190_203.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___190_203.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___190_203.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___190_203.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___190_203.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___190_203.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___190_203.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___190_203.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___190_203.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___190_203.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___190_203.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___190_203.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___190_203.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___190_203.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___190_203.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___190_203.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.type_of =
          (uu___190_203.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___190_203.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___190_203.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___190_203.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___190_203.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___190_203.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___190_203.FStar_TypeChecker_Env.identifier_info)
      } in
    (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env2;
    (let prims_filename = FStar_Options.prims () in
     let uu____206 =
       let uu____213 = FStar_ToSyntax_Env.empty_env () in
       parse uu____213 FStar_Pervasives_Native.None prims_filename in
     match uu____206 with
     | (dsenv,prims_mod) ->
         let uu____230 =
           FStar_Util.record_time
             (fun uu____245  ->
                let uu____246 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env2 uu____246) in
         (match uu____230 with
          | ((prims_mod1,env3),elapsed_time) ->
              ((prims_mod1, elapsed_time), dsenv, env3)))
let tc_one_fragment:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_ToSyntax_Env.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_Parser_ParseIt.input_frag,Prims.bool)
          FStar_Pervasives_Native.tuple2 ->
          (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option,FStar_ToSyntax_Env.env,
            FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option
  =
  fun curmod  ->
    fun dsenv  ->
      fun env  ->
        fun uu____299  ->
          match uu____299 with
          | (frag,is_interface_dependence) ->
              (try
                 let uu____341 = FStar_Parser_Driver.parse_fragment frag in
                 match uu____341 with
                 | FStar_Parser_Driver.Empty  ->
                     FStar_Pervasives_Native.Some (curmod, dsenv, env)
                 | FStar_Parser_Driver.Modul ast_modul ->
                     let uu____363 =
                       FStar_ToSyntax_Interleave.interleave_module dsenv
                         ast_modul false in
                     (match uu____363 with
                      | (ds_env,ast_modul1) ->
                          let uu____380 =
                            FStar_ToSyntax_ToSyntax.desugar_partial_modul
                              curmod dsenv ast_modul1 in
                          (match uu____380 with
                           | (dsenv1,modul) ->
                               let dsenv2 =
                                 if is_interface_dependence
                                 then
                                   FStar_ToSyntax_Env.set_iface dsenv1 false
                                 else dsenv1 in
                               let env1 =
                                 match curmod with
                                 | FStar_Pervasives_Native.Some modul1 ->
                                     let uu____401 =
                                       let uu____402 =
                                         let uu____403 =
                                           let uu____404 =
                                             FStar_Options.file_list () in
                                           FStar_List.hd uu____404 in
                                         FStar_Parser_Dep.lowercase_module_name
                                           uu____403 in
                                       let uu____407 =
                                         let uu____408 =
                                           FStar_Ident.string_of_lid
                                             modul1.FStar_Syntax_Syntax.name in
                                         FStar_String.lowercase uu____408 in
                                       uu____402 <> uu____407 in
                                     if uu____401
                                     then
                                       FStar_Exn.raise
                                         (FStar_Errors.Err
                                            "Interactive mode only supports a single module at the top-level")
                                     else env
                                 | FStar_Pervasives_Native.None  -> env in
                               let uu____410 =
                                 let uu____419 =
                                   FStar_ToSyntax_Env.syntax_only dsenv2 in
                                 if uu____419
                                 then (modul, [], env1)
                                 else
                                   FStar_TypeChecker_Tc.tc_partial_modul env1
                                     modul in
                               (match uu____410 with
                                | (modul1,uu____442,env2) ->
                                    FStar_Pervasives_Native.Some
                                      ((FStar_Pervasives_Native.Some modul1),
                                        dsenv2, env2))))
                 | FStar_Parser_Driver.Decls ast_decls ->
                     let uu____461 =
                       FStar_Util.fold_map
                         FStar_ToSyntax_Interleave.prefix_with_interface_decls
                         dsenv ast_decls in
                     (match uu____461 with
                      | (dsenv1,ast_decls_l) ->
                          let uu____492 =
                            FStar_ToSyntax_ToSyntax.desugar_decls dsenv1
                              (FStar_List.flatten ast_decls_l) in
                          (match uu____492 with
                           | (dsenv2,decls) ->
                               (match curmod with
                                | FStar_Pervasives_Native.None  ->
                                    (FStar_Util.print_error
                                       "fragment without an enclosing module";
                                     FStar_All.exit (Prims.parse_int "1"))
                                | FStar_Pervasives_Native.Some modul ->
                                    let uu____531 =
                                      let uu____540 =
                                        FStar_ToSyntax_Env.syntax_only dsenv2 in
                                      if uu____540
                                      then (modul, [], env)
                                      else
                                        FStar_TypeChecker_Tc.tc_more_partial_modul
                                          env modul decls in
                                    (match uu____531 with
                                     | (modul1,uu____563,env1) ->
                                         FStar_Pervasives_Native.Some
                                           ((FStar_Pervasives_Native.Some
                                               modul1), dsenv2, env1)))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____596 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____596 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                    FStar_Pervasives_Native.None)
               | FStar_Errors.Err msg when
                   let uu____615 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____615 ->
                   (FStar_TypeChecker_Err.add_errors env
                      [(msg, FStar_Range.dummyRange)];
                    FStar_Pervasives_Native.None)
               | e when
                   let uu____634 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____634 -> FStar_Exn.raise e)
let load_interface_decls:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_ParseIt.filename ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____659  ->
    fun interface_file_name  ->
      match uu____659 with
      | (dsenv,env) ->
          (try
             let r =
               FStar_Parser_ParseIt.parse
                 (FStar_Util.Inl interface_file_name) in
             match r with
             | FStar_Util.Inl
                 (FStar_Util.Inl ((FStar_Parser_AST.Interface
                  (l,decls,uu____716))::[]),uu____717)
                 ->
                 let uu____768 =
                   FStar_ToSyntax_Interleave.initialize_interface l decls
                     dsenv in
                 (uu____768, env)
             | FStar_Util.Inl uu____769 ->
                 let uu____794 =
                   let uu____795 =
                     FStar_Util.format1
                       "Unexpected result from parsing %s; expected a single interface"
                       interface_file_name in
                   FStar_Errors.Err uu____795 in
                 FStar_Exn.raise uu____794
             | FStar_Util.Inr (err1,rng) ->
                 FStar_Exn.raise (FStar_Errors.Error (err1, rng))
           with
           | FStar_Errors.Error (msg,r) when
               let uu____831 = FStar_Options.trace_error () in
               Prims.op_Negation uu____831 ->
               (FStar_TypeChecker_Err.add_errors env [(msg, r)]; (dsenv, env))
           | FStar_Errors.Err msg when
               let uu____842 = FStar_Options.trace_error () in
               Prims.op_Negation uu____842 ->
               (FStar_TypeChecker_Err.add_errors env
                  [(msg, FStar_Range.dummyRange)];
                (dsenv, env))
           | e when
               let uu____853 = FStar_Options.trace_error () in
               Prims.op_Negation uu____853 -> FStar_Exn.raise e)
let tc_one_file:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((FStar_Syntax_Syntax.modul,Prims.int)
             FStar_Pervasives_Native.tuple2 Prims.list,FStar_ToSyntax_Env.env,
            FStar_TypeChecker_Env.env) FStar_Pervasives_Native.tuple3
  =
  fun dsenv  ->
    fun env  ->
      fun pre_fn  ->
        fun fn  ->
          let uu____902 = parse dsenv pre_fn fn in
          match uu____902 with
          | (dsenv1,fmods) ->
              let check_mods uu____942 =
                let uu____943 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
                       (fun uu____984  ->
                          fun m  ->
                            match uu____984 with
                            | (env1,all_mods) ->
                                let uu____1020 =
                                  FStar_Util.record_time
                                    (fun uu____1034  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____1020 with
                                 | ((m1,env2),elapsed_ms) ->
                                     (env2, ((m1, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____943 with
                | (env1,all_mods) ->
                    ((FStar_List.rev all_mods), dsenv1, env1) in
              (match fmods with
               | m::[] when
                   (FStar_Options.should_verify
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                   ->
                   let uu____1121 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1121
                     check_mods
               | uu____1134 -> check_mods ())
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1148 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1148 ["fsti"; "fsi"]))
        &&
        (let uu____1150 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1150 ["fst"; "fs"])
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____1160 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____1160 FStar_Pervasives.ignore);
      (let uu____1162 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____1162 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1177  ->
    fun msg  ->
      match uu____1177 with
      | (dsenv,env) ->
          let dsenv1 = FStar_ToSyntax_Env.push dsenv in
          let env1 = FStar_TypeChecker_Env.push env msg in (dsenv1, env1)
type uenv =
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2
let tc_one_file_from_remaining:
  Prims.string Prims.list ->
    uenv ->
      (Prims.string Prims.list,(FStar_Syntax_Syntax.modul,Prims.int)
                                 FStar_Pervasives_Native.tuple2 Prims.list,
        (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2)
        FStar_Pervasives_Native.tuple3
  =
  fun remaining  ->
    fun uenv  ->
      let uu____1225 = uenv in
      match uu____1225 with
      | (dsenv,env) ->
          let uu____1246 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____1288 =
                  tc_one_file dsenv env (FStar_Pervasives_Native.Some intf)
                    impl in
                (remaining1, uu____1288)
            | intf_or_impl::remaining1 ->
                let uu____1319 =
                  tc_one_file dsenv env FStar_Pervasives_Native.None
                    intf_or_impl in
                (remaining1, uu____1319)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____1246 with
           | (remaining1,(nmods,dsenv1,env1)) ->
               (remaining1, nmods, (dsenv1, env1)))
let rec tc_fold_interleave:
  ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
     Prims.list,uenv)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string Prims.list ->
      ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
         Prims.list,uenv)
        FStar_Pervasives_Native.tuple2
  =
  fun acc  ->
    fun remaining  ->
      match remaining with
      | [] -> acc
      | uu____1484 ->
          let uu____1487 = acc in
          (match uu____1487 with
           | (mods,uenv) ->
               let uu____1522 = tc_one_file_from_remaining remaining uenv in
               (match uu____1522 with
                | (remaining1,nmods,(dsenv,env)) ->
                    tc_fold_interleave
                      ((FStar_List.append mods nmods), (dsenv, env))
                      remaining1))
let batch_mode_tc_no_prims:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env ->
      Prims.string Prims.list ->
        ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
           Prims.list,FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple3
  =
  fun dsenv  ->
    fun env  ->
      fun filenames  ->
        let uu____1617 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____1617 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____1674 =
                (FStar_Options.interactive ()) &&
                  (let uu____1676 = FStar_Errors.get_err_count () in
                   uu____1676 = (Prims.parse_int "0")) in
              if uu____1674
              then
                (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ()
              else
                (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                  ());
             (all_mods, dsenv1, env1))
let batch_mode_tc:
  Prims.string Prims.list ->
    ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2
       Prims.list,FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple3
  =
  fun filenames  ->
    let uu____1704 = tc_prims () in
    match uu____1704 with
    | (prims_mod,dsenv,env) ->
        ((let uu____1739 =
            (let uu____1742 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1742) && (FStar_Options.debug_any ()) in
          if uu____1739
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1745 =
                let uu____1746 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1746 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1745))
          else ());
         (let uu____1750 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____1750 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))