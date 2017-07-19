open Prims
let module_or_interface_name:
  FStar_Syntax_Syntax.modul ->
    (Prims.bool,FStar_Ident.lident) FStar_Pervasives_Native.tuple2
  =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
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
        let uu____33 = FStar_Parser_Driver.parse_file fn in
        match uu____33 with
        | (ast,uu____51) ->
            let uu____64 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (env, ast)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____74 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____74 with
                   | (pre_ast,uu____90) ->
                       (match (pre_ast, ast) with
                        | ((FStar_Parser_AST.Interface
                           (lid1,decls1,uu____109))::[],(FStar_Parser_AST.Module
                           (lid2,decls2))::[]) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let env1 =
                              FStar_ToSyntax_Interleave.initialize_interface
                                lid1 decls1 env in
                            let uu____125 =
                              let uu____130 = FStar_List.hd ast in
                              FStar_ToSyntax_Interleave.interleave_module
                                env1 uu____130 true in
                            (match uu____125 with
                             | (env2,ast1) -> (env2, [ast1]))
                        | uu____139 ->
                            raise
                              (FStar_Errors.Err
                                 "mismatch between pre-module and module\n"))) in
            (match uu____64 with
             | (env1,ast1) -> FStar_ToSyntax_ToSyntax.desugar_file env1 ast1)
let tc_prims:
  Prims.unit ->
    ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2,
      FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple3
  =
  fun uu____168  ->
    let solver1 =
      let uu____180 = FStar_Options.lax () in
      if uu____180
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___193_182 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___193_182.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___193_182.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___193_182.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___193_182.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___193_182.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___193_182.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___193_182.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___193_182.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___193_182.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___193_182.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___193_182.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___193_182.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Parser_Const.prims_lid in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let prims_filename = FStar_Options.prims () in
     let uu____186 =
       let uu____193 = FStar_ToSyntax_Env.empty_env () in
       parse uu____193 FStar_Pervasives_Native.None prims_filename in
     match uu____186 with
     | (dsenv,prims_mod) ->
         let uu____210 =
           FStar_Util.record_time
             (fun uu____223  ->
                let uu____224 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env uu____224) in
         (match uu____210 with
          | ((prims_mod1,env1),elapsed_time) ->
              ((prims_mod1, elapsed_time), dsenv, env1)))
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
        fun uu____273  ->
          match uu____273 with
          | (frag,is_interface_dependence) ->
              (try
                 let uu____313 = FStar_Parser_Driver.parse_fragment frag in
                 match uu____313 with
                 | FStar_Parser_Driver.Empty  ->
                     FStar_Pervasives_Native.Some (curmod, dsenv, env)
                 | FStar_Parser_Driver.Modul ast_modul ->
                     let uu____335 =
                       FStar_ToSyntax_Interleave.interleave_module dsenv
                         ast_modul false in
                     (match uu____335 with
                      | (ds_env,ast_modul1) ->
                          let uu____352 =
                            FStar_ToSyntax_ToSyntax.desugar_partial_modul
                              curmod dsenv ast_modul1 in
                          (match uu____352 with
                           | (dsenv1,modul) ->
                               let dsenv2 =
                                 if is_interface_dependence
                                 then
                                   FStar_ToSyntax_Env.set_iface dsenv1 false
                                 else dsenv1 in
                               let env1 =
                                 match curmod with
                                 | FStar_Pervasives_Native.Some modul1 ->
                                     let uu____373 =
                                       let uu____374 =
                                         let uu____375 =
                                           let uu____376 =
                                             FStar_Options.file_list () in
                                           FStar_List.hd uu____376 in
                                         FStar_Parser_Dep.lowercase_module_name
                                           uu____375 in
                                       let uu____379 =
                                         let uu____380 =
                                           FStar_Ident.string_of_lid
                                             modul1.FStar_Syntax_Syntax.name in
                                         FStar_String.lowercase uu____380 in
                                       uu____374 <> uu____379 in
                                     if uu____373
                                     then
                                       raise
                                         (FStar_Errors.Err
                                            "Interactive mode only supports a single module at the top-level")
                                     else env
                                 | FStar_Pervasives_Native.None  -> env in
                               let uu____382 =
                                 let uu____391 =
                                   FStar_ToSyntax_Env.syntax_only dsenv2 in
                                 if uu____391
                                 then (modul, [], env1)
                                 else
                                   FStar_TypeChecker_Tc.tc_partial_modul env1
                                     modul in
                               (match uu____382 with
                                | (modul1,uu____414,env2) ->
                                    FStar_Pervasives_Native.Some
                                      ((FStar_Pervasives_Native.Some modul1),
                                        dsenv2, env2))))
                 | FStar_Parser_Driver.Decls ast_decls ->
                     let uu____433 =
                       FStar_Util.fold_map
                         FStar_ToSyntax_Interleave.prefix_with_interface_decls
                         dsenv ast_decls in
                     (match uu____433 with
                      | (dsenv1,ast_decls_l) ->
                          let uu____464 =
                            FStar_ToSyntax_ToSyntax.desugar_decls dsenv1
                              (FStar_List.flatten ast_decls_l) in
                          (match uu____464 with
                           | (dsenv2,decls) ->
                               (match curmod with
                                | FStar_Pervasives_Native.None  ->
                                    (FStar_Util.print_error
                                       "fragment without an enclosing module";
                                     FStar_All.exit (Prims.parse_int "1"))
                                | FStar_Pervasives_Native.Some modul ->
                                    let uu____503 =
                                      let uu____512 =
                                        FStar_ToSyntax_Env.syntax_only dsenv2 in
                                      if uu____512
                                      then (modul, [], env)
                                      else
                                        FStar_TypeChecker_Tc.tc_more_partial_modul
                                          env modul decls in
                                    (match uu____503 with
                                     | (modul1,uu____535,env1) ->
                                         FStar_Pervasives_Native.Some
                                           ((FStar_Pervasives_Native.Some
                                               modul1), dsenv2, env1)))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____564 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____564 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                    FStar_Pervasives_Native.None)
               | FStar_Errors.Err msg when
                   let uu____583 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____583 ->
                   (FStar_TypeChecker_Err.add_errors env
                      [(msg, FStar_Range.dummyRange)];
                    FStar_Pervasives_Native.None)
               | e when
                   let uu____602 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____602 -> raise e)
let load_interface_decls:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_ParseIt.filename ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____625  ->
    fun interface_file_name  ->
      match uu____625 with
      | (dsenv,env) ->
          (try
             let r =
               FStar_Parser_ParseIt.parse
                 (FStar_Util.Inl interface_file_name) in
             match r with
             | FStar_Util.Inl
                 (FStar_Util.Inl ((FStar_Parser_AST.Interface
                  (l,decls,uu____675))::[]),uu____676)
                 ->
                 let uu____727 =
                   FStar_ToSyntax_Interleave.initialize_interface l decls
                     dsenv in
                 (uu____727, env)
             | FStar_Util.Inl uu____728 ->
                 let uu____753 =
                   let uu____754 =
                     FStar_Util.format1
                       "Unexpected result from parsing %s; expected a single interface"
                       interface_file_name in
                   FStar_Errors.Err uu____754 in
                 raise uu____753
             | FStar_Util.Inr (err1,rng) ->
                 raise (FStar_Errors.Error (err1, rng))
           with
           | FStar_Errors.Error (msg,r) when
               let uu____786 = FStar_Options.trace_error () in
               Prims.op_Negation uu____786 ->
               (FStar_TypeChecker_Err.add_errors env [(msg, r)]; (dsenv, env))
           | FStar_Errors.Err msg when
               let uu____797 = FStar_Options.trace_error () in
               Prims.op_Negation uu____797 ->
               (FStar_TypeChecker_Err.add_errors env
                  [(msg, FStar_Range.dummyRange)];
                (dsenv, env))
           | e when
               let uu____808 = FStar_Options.trace_error () in
               Prims.op_Negation uu____808 -> raise e)
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
          let uu____853 = parse dsenv pre_fn fn in
          match uu____853 with
          | (dsenv1,fmods) ->
              let check_mods uu____893 =
                let uu____894 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
                       (fun uu____927  ->
                          fun m  ->
                            match uu____927 with
                            | (env1,all_mods) ->
                                let uu____963 =
                                  FStar_Util.record_time
                                    (fun uu____976  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____963 with
                                 | ((m1,env2),elapsed_ms) ->
                                     (env2, ((m1, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____894 with
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
                   let uu____1063 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____1063
                     check_mods
               | uu____1076 -> check_mods ())
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1087 = FStar_Util.get_file_extension intf in
          uu____1087 = "fsti"))
        &&
        (let uu____1088 = FStar_Util.get_file_extension impl in
         uu____1088 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____1096 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____1096 FStar_Pervasives.ignore);
      (let uu____1098 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____1098 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1111  ->
    fun msg  ->
      match uu____1111 with
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
      let uu____1157 = uenv in
      match uu____1157 with
      | (dsenv,env) ->
          let uu____1178 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____1220 =
                  tc_one_file dsenv env (FStar_Pervasives_Native.Some intf)
                    impl in
                (remaining1, uu____1220)
            | intf_or_impl::remaining1 ->
                let uu____1251 =
                  tc_one_file dsenv env FStar_Pervasives_Native.None
                    intf_or_impl in
                (remaining1, uu____1251)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____1178 with
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
      | uu____1414 ->
          let uu____1417 = acc in
          (match uu____1417 with
           | (mods,uenv) ->
               let uu____1452 = tc_one_file_from_remaining remaining uenv in
               (match uu____1452 with
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
        let uu____1544 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____1544 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____1601 =
                (FStar_Options.interactive ()) &&
                  (let uu____1602 = FStar_Errors.get_err_count () in
                   uu____1602 = (Prims.parse_int "0")) in
              if uu____1601
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
    let uu____1629 = tc_prims () in
    match uu____1629 with
    | (prims_mod,dsenv,env) ->
        ((let uu____1664 =
            (let uu____1665 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1665) && (FStar_Options.debug_any ()) in
          if uu____1664
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1668 =
                let uu____1669 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1669 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1668))
          else ());
         (let uu____1673 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____1673 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))