open Prims
let module_or_interface_name:
  FStar_Syntax_Syntax.modul -> (Prims.bool* FStar_Ident.lident) =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
let parse:
  FStar_ToSyntax_Env.env ->
    Prims.string Prims.option ->
      Prims.string ->
        (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____23 = FStar_Parser_Driver.parse_file fn in
        match uu____23 with
        | (ast,uu____33) ->
            let ast1 =
              match pre_fn with
              | None  -> ast
              | Some pre_fn1 ->
                  let uu____42 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____42 with
                   | (pre_ast,uu____49) ->
                       (match (pre_ast, ast) with
                        | ((FStar_Parser_AST.Interface
                           (lid1,decls1,uu____58))::[],(FStar_Parser_AST.Module
                           (lid2,decls2))::[]) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu____67 =
                              let uu____68 =
                                let uu____72 =
                                  FStar_Parser_Interleave.interleave decls1
                                    decls2 in
                                (lid1, uu____72) in
                              FStar_Parser_AST.Module uu____68 in
                            [uu____67]
                        | uu____75 ->
                            Prims.raise
                              (FStar_Errors.Err
                                 "mismatch between pre-module and module\n"))) in
            FStar_ToSyntax_ToSyntax.desugar_file env ast1
let tc_prims:
  Prims.unit ->
    ((FStar_Syntax_Syntax.modul* Prims.int)* FStar_ToSyntax_Env.env*
      FStar_TypeChecker_Env.env)
  =
  fun uu____85  ->
    let solver1 =
      let uu____92 = FStar_Options.lax () in
      if uu____92
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___216_94 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___216_94.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___216_94.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___216_94.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___216_94.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___216_94.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___216_94.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___216_94.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___216_94.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___216_94.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___216_94.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___216_94.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___216_94.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Syntax_Const.prims_lid in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let prims_filename = FStar_Options.prims () in
     let uu____98 =
       let uu____102 = FStar_ToSyntax_Env.empty_env () in
       parse uu____102 None prims_filename in
     match uu____98 with
     | (dsenv,prims_mod) ->
         let uu____112 =
           FStar_Util.record_time
             (fun uu____119  ->
                let uu____120 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env uu____120) in
         (match uu____112 with
          | ((prims_mod1,env1),elapsed_time) ->
              ((prims_mod1, elapsed_time), dsenv, env1)))
let tc_one_fragment:
  FStar_Syntax_Syntax.modul Prims.option ->
    FStar_ToSyntax_Env.env ->
      FStar_TypeChecker_Env.env ->
        FStar_Parser_ParseIt.input_frag ->
          (FStar_Syntax_Syntax.modul Prims.option* FStar_ToSyntax_Env.env*
            FStar_TypeChecker_Env.env) Prims.option
  =
  fun curmod  ->
    fun dsenv  ->
      fun env  ->
        fun frag  ->
          try
            let uu____163 = FStar_Parser_Driver.parse_fragment frag in
            match uu____163 with
            | FStar_Parser_Driver.Empty  -> Some (curmod, dsenv, env)
            | FStar_Parser_Driver.Modul ast_modul ->
                let uu____175 =
                  FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv
                    ast_modul in
                (match uu____175 with
                 | (dsenv1,modul) ->
                     let env1 =
                       match curmod with
                       | Some modul1 ->
                           let uu____187 =
                             let uu____188 =
                               let uu____189 =
                                 let uu____190 = FStar_Options.file_list () in
                                 FStar_List.hd uu____190 in
                               FStar_Parser_Dep.lowercase_module_name
                                 uu____189 in
                             let uu____192 =
                               let uu____193 =
                                 FStar_Ident.string_of_lid
                                   modul1.FStar_Syntax_Syntax.name in
                               FStar_String.lowercase uu____193 in
                             uu____188 <> uu____192 in
                           if uu____187
                           then
                             Prims.raise
                               (FStar_Errors.Err
                                  "Interactive mode only supports a single module at the top-level")
                           else env
                       | None  -> env in
                     let uu____195 =
                       FStar_TypeChecker_Tc.tc_partial_modul env1 modul in
                     (match uu____195 with
                      | (modul1,uu____206,env2) ->
                          Some ((Some modul1), dsenv1, env2)))
            | FStar_Parser_Driver.Decls ast_decls ->
                let uu____217 =
                  FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls in
                (match uu____217 with
                 | (dsenv1,decls) ->
                     (match curmod with
                      | None  ->
                          (FStar_Util.print_error
                             "fragment without an enclosing module";
                           FStar_All.exit (Prims.parse_int "1"))
                      | Some modul ->
                          let uu____239 =
                            FStar_TypeChecker_Tc.tc_more_partial_modul env
                              modul decls in
                          (match uu____239 with
                           | (modul1,uu____250,env1) ->
                               Some ((Some modul1), dsenv1, env1))))
          with
          | FStar_Errors.Error (msg,r) when
              let uu____267 = FStar_Options.trace_error () in
              Prims.op_Negation uu____267 ->
              (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
          | FStar_Errors.Err msg when
              let uu____278 = FStar_Options.trace_error () in
              Prims.op_Negation uu____278 ->
              (FStar_TypeChecker_Err.add_errors env
                 [(msg, FStar_Range.dummyRange)];
               None)
          | e when
              let uu____289 = FStar_Options.trace_error () in
              Prims.op_Negation uu____289 -> Prims.raise e
let tc_one_file:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env ->
      Prims.string Prims.option ->
        Prims.string ->
          Prims.bool ->
            ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
              FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env* Prims.bool)
  =
  fun dsenv  ->
    fun env  ->
      fun pre_fn  ->
        fun fn  ->
          fun use_cache  ->
            let uu____326 = parse dsenv pre_fn fn in
            match uu____326 with
            | (dsenv1,fmods) ->
                let check_mods fmods1 uu____354 =
                  let uu____356 =
                    FStar_All.pipe_right fmods1
                      (FStar_List.fold_left
                         (fun uu____373  ->
                            fun m  ->
                              match uu____373 with
                              | (env1,all_mods) ->
                                  let uu____393 =
                                    FStar_Util.record_time
                                      (fun uu____400  ->
                                         FStar_TypeChecker_Tc.check_module
                                           env1 m) in
                                  (match uu____393 with
                                   | ((m1,env2),elapsed_ms) ->
                                       (env2, ((m1, elapsed_ms) :: all_mods))))
                         (env, [])) in
                  match uu____356 with
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
                     let uu____448 =
                       let uu____455 = FStar_Parser_ParseIt.find_file fn in
                       FStar_SMTEncoding_Solver.with_hints_db uu____455
                         (check_mods fmods) in
                     (match uu____448 with
                      | (all_mods,dsenv2,env1) ->
                          (all_mods, dsenv2, env1, use_cache))
                 | m::[] when
                     let uu____482 =
                       FStar_Options.should_verify
                         (m.FStar_Syntax_Syntax.name).FStar_Ident.str in
                     Prims.op_Negation uu____482 ->
                     let get_lax_cache_file_name fn1 =
                       let fn2 = FStar_Util.normalize_file_path fn1 in
                       FStar_Util.format1 "%s.lax.out" fn2 in
                     let read_cache fn1 cache_fn =
                       (use_cache && (FStar_Util.file_exists cache_fn)) &&
                         (let uu____495 =
                            FStar_Util.get_file_last_modification_time fn1 in
                          let uu____496 =
                            FStar_Util.get_file_last_modification_time
                              cache_fn in
                          FStar_Util.is_before uu____495 uu____496) in
                     let fn1 = FStar_Parser_ParseIt.find_file fn in
                     let cache_fn = get_lax_cache_file_name fn1 in
                     let uu____499 =
                       let uu____503 = read_cache fn1 cache_fn in
                       if uu____503
                       then
                         (FStar_Util.print_string
                            (Prims.strcat "Using the cache file: "
                               (Prims.strcat cache_fn ", loading module\n"));
                          (let uu____508 =
                             FStar_Util.load_value_from_file cache_fn in
                           match uu____508 with
                           | Some m1 ->
                               ([(let uu___219_515 = m1 in
                                  {
                                    FStar_Syntax_Syntax.name =
                                      (uu___219_515.FStar_Syntax_Syntax.name);
                                    FStar_Syntax_Syntax.declarations =
                                      (uu___219_515.FStar_Syntax_Syntax.declarations);
                                    FStar_Syntax_Syntax.exports =
                                      (uu___219_515.FStar_Syntax_Syntax.exports);
                                    FStar_Syntax_Syntax.is_interface =
                                      (uu___219_515.FStar_Syntax_Syntax.is_interface);
                                    FStar_Syntax_Syntax.lax_deserialized =
                                      true
                                  })], true)
                           | None  ->
                               (FStar_Util.print_string
                                  (Prims.strcat
                                     "Failed to load the module from the cache file: "
                                     (Prims.strcat cache_fn "\n"));
                                (fmods, false))))
                       else
                         (FStar_Util.print_string
                            (Prims.strcat "Not using the cache file: "
                               (Prims.strcat cache_fn "\n"));
                          (fmods, false)) in
                     (match uu____499 with
                      | (fmods1,cache_ok) ->
                          let uu____532 = check_mods fmods1 () in
                          (match uu____532 with
                           | (l,dsenv2,env1) ->
                               ((let uu____556 =
                                   (Prims.op_Negation cache_ok) &&
                                     (FStar_Options.serialize_lax ()) in
                                 if uu____556
                                 then
                                   (if
                                      Prims.op_Negation
                                        ((FStar_List.length l) =
                                           (Prims.parse_int "1"))
                                    then
                                      failwith
                                        "Impossible, expected a single module"
                                    else ();
                                    (let uu____563 = FStar_List.hd l in
                                     match uu____563 with
                                     | (m1,uu____569) ->
                                         (FStar_Util.print_string
                                            (Prims.strcat
                                               "Serializing the cache file: "
                                               (Prims.strcat cache_fn "\n"));
                                          FStar_Util.save_value_to_file
                                            cache_fn m1)))
                                 else ());
                                (l, dsenv2, env1, cache_ok))))
                 | uu____575 ->
                     let uu____577 = check_mods fmods () in
                     (match uu____577 with
                      | (all_mods,dsenv2,env1) ->
                          (all_mods, dsenv2, env1, use_cache)))
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____611 = FStar_Util.get_file_extension intf in
          uu____611 = "fsti"))
        &&
        (let uu____612 = FStar_Util.get_file_extension impl in
         uu____612 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____620 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____620 Prims.ignore);
      (let uu____622 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____622 Prims.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____631  ->
    fun msg  ->
      match uu____631 with
      | (dsenv,env) ->
          let dsenv1 = FStar_ToSyntax_Env.push dsenv in
          let env1 = FStar_TypeChecker_Env.push env msg in (dsenv1, env1)
let tc_one_file_and_intf:
  Prims.string Prims.option ->
    Prims.string ->
      FStar_ToSyntax_Env.env ->
        FStar_TypeChecker_Env.env ->
          Prims.bool ->
            ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
              FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env* Prims.bool)
  =
  fun intf  ->
    fun impl  ->
      fun dsenv  ->
        fun env  ->
          fun use_cache  ->
            FStar_Syntax_Syntax.reset_gensym ();
            (match intf with
             | None  -> tc_one_file dsenv env None impl use_cache
             | Some uu____673 when
                 let uu____674 = FStar_Options.codegen () in
                 uu____674 <> None ->
                 ((let uu____678 =
                     let uu____679 = FStar_Options.lax () in
                     Prims.op_Negation uu____679 in
                   if uu____678
                   then
                     Prims.raise
                       (FStar_Errors.Err
                          "Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")
                   else ());
                  tc_one_file dsenv env intf impl use_cache)
             | Some iname ->
                 ((let uu____683 = FStar_Options.debug_any () in
                   if uu____683
                   then
                     FStar_Util.print1 "Interleaving iface+module: %s\n"
                       iname
                   else ());
                  (let caption = Prims.strcat "interface: " iname in
                   let uu____686 = push_context (dsenv, env) caption in
                   match uu____686 with
                   | (dsenv',env') ->
                       let uu____698 =
                         tc_one_file dsenv' env' intf impl use_cache in
                       (match uu____698 with
                        | (uu____713,dsenv'1,env'1,use_cache1) ->
                            (pop_context env'1 caption;
                             tc_one_file dsenv env None iname use_cache1)))))
type uenv = (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
let tc_one_file_from_remaining:
  Prims.string Prims.list ->
    uenv ->
      Prims.bool ->
        (Prims.string Prims.list* (FStar_Syntax_Syntax.modul* Prims.int)
          Prims.list* (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)*
          Prims.bool)
  =
  fun remaining  ->
    fun uenv  ->
      fun use_cache  ->
        let uu____747 = uenv in
        match uu____747 with
        | (dsenv,env) ->
            let uu____760 =
              match remaining with
              | intf::impl::remaining1 when needs_interleaving intf impl ->
                  let uu____785 =
                    tc_one_file_and_intf (Some intf) impl dsenv env use_cache in
                  (remaining1, uu____785)
              | intf_or_impl::remaining1 ->
                  let uu____804 =
                    tc_one_file_and_intf None intf_or_impl dsenv env
                      use_cache in
                  (remaining1, uu____804)
              | [] -> ([], ([], dsenv, env, use_cache)) in
            (match uu____760 with
             | (remaining1,(nmods,dsenv1,env1,use_cache1)) ->
                 (remaining1, nmods, (dsenv1, env1), use_cache1))
let rec tc_fold_interleave:
  ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list* uenv* Prims.bool) ->
    Prims.string Prims.list ->
      ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list* uenv* Prims.bool)
  =
  fun acc  ->
    fun remaining  ->
      match remaining with
      | [] -> acc
      | uu____901 ->
          let uu____903 = acc in
          (match uu____903 with
           | (mods,uenv,use_cache) ->
               let uu____925 =
                 tc_one_file_from_remaining remaining uenv use_cache in
               (match uu____925 with
                | (remaining1,nmods,(dsenv,env),use_cache1) ->
                    tc_fold_interleave
                      ((FStar_List.append mods nmods), (dsenv, env),
                        use_cache1) remaining1))
let batch_mode_tc_no_prims:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env ->
      Prims.string Prims.list ->
        ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
          FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun dsenv  ->
    fun env  ->
      fun filenames  ->
        let uu____981 = tc_fold_interleave ([], (dsenv, env), true) filenames in
        match uu____981 with
        | (all_mods,(dsenv1,env1),uu____1004) ->
            ((let uu____1014 =
                (FStar_Options.interactive ()) &&
                  (let uu____1015 = FStar_Errors.get_err_count () in
                   uu____1015 = (Prims.parse_int "0")) in
              if uu____1014
              then
                (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ()
              else
                (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                  ());
             (all_mods, dsenv1, env1))
let batch_mode_tc:
  Prims.string Prims.list ->
    ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
      FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun filenames  ->
    let uu____1031 = tc_prims () in
    match uu____1031 with
    | (prims_mod,dsenv,env) ->
        ((let uu____1051 =
            (let uu____1052 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1052) && (FStar_Options.debug_any ()) in
          if uu____1051
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1055 =
                let uu____1056 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1056 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1055))
          else ());
         (let uu____1059 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____1059 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))