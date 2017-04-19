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
            let uu____40 =
              match pre_fn with
              | None  -> (env, ast)
              | Some pre_fn1 ->
                  let uu____46 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____46 with
                   | (pre_ast,uu____55) ->
                       (match (pre_ast, ast) with
                        | ((FStar_Parser_AST.Interface
                           (lid1,decls1,uu____66))::[],(FStar_Parser_AST.Module
                           (lid2,decls2))::[]) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let env1 =
                              FStar_ToSyntax_Interleave.initialize_interface
                                lid1 decls1 env in
                            let uu____76 =
                              let uu____79 = FStar_List.hd ast in
                              FStar_ToSyntax_Interleave.interleave_module
                                env1 uu____79 true in
                            (match uu____76 with
                             | (env2,ast1) -> (env2, [ast1]))
                        | uu____85 ->
                            Prims.raise
                              (FStar_Errors.Err
                                 "mismatch between pre-module and module\n"))) in
            (match uu____40 with
             | (env1,ast1) -> FStar_ToSyntax_ToSyntax.desugar_file env1 ast1)
let tc_prims:
  Prims.unit ->
    ((FStar_Syntax_Syntax.modul* Prims.int)* FStar_ToSyntax_Env.env*
      FStar_TypeChecker_Env.env)
  =
  fun uu____102  ->
    let solver1 =
      let uu____109 = FStar_Options.lax () in
      if uu____109
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___218_111 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___218_111.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___218_111.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___218_111.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___218_111.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___218_111.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___218_111.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___218_111.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___218_111.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___218_111.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___218_111.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___218_111.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___218_111.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Syntax_Const.prims_lid in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let prims_filename = FStar_Options.prims () in
     let uu____115 =
       let uu____119 = FStar_ToSyntax_Env.empty_env () in
       parse uu____119 None prims_filename in
     match uu____115 with
     | (dsenv,prims_mod) ->
         let uu____129 =
           FStar_Util.record_time
             (fun uu____136  ->
                let uu____137 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env uu____137) in
         (match uu____129 with
          | ((prims_mod1,env1),elapsed_time) ->
              ((prims_mod1, elapsed_time), dsenv, env1)))
let tc_one_fragment:
  FStar_Syntax_Syntax.modul Prims.option ->
    FStar_ToSyntax_Env.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_Parser_ParseIt.input_frag* Prims.bool) ->
          (FStar_Syntax_Syntax.modul Prims.option* FStar_ToSyntax_Env.env*
            FStar_TypeChecker_Env.env) Prims.option
  =
  fun curmod  ->
    fun dsenv  ->
      fun env  ->
        fun uu____169  ->
          match uu____169 with
          | (frag,is_interface_dependence) ->
              (try
                 let uu____191 = FStar_Parser_Driver.parse_fragment frag in
                 match uu____191 with
                 | FStar_Parser_Driver.Empty  -> Some (curmod, dsenv, env)
                 | FStar_Parser_Driver.Modul ast_modul ->
                     let uu____203 =
                       FStar_ToSyntax_Interleave.interleave_module dsenv
                         ast_modul false in
                     (match uu____203 with
                      | (ds_env,ast_modul1) ->
                          let uu____213 =
                            FStar_ToSyntax_ToSyntax.desugar_partial_modul
                              curmod dsenv ast_modul1 in
                          (match uu____213 with
                           | (dsenv1,modul) ->
                               let dsenv2 =
                                 if is_interface_dependence
                                 then
                                   FStar_ToSyntax_Env.set_iface dsenv1 false
                                 else dsenv1 in
                               let env1 =
                                 match curmod with
                                 | Some modul1 ->
                                     let uu____227 =
                                       let uu____228 =
                                         let uu____229 =
                                           let uu____230 =
                                             FStar_Options.file_list () in
                                           FStar_List.hd uu____230 in
                                         FStar_Parser_Dep.lowercase_module_name
                                           uu____229 in
                                       let uu____232 =
                                         let uu____233 =
                                           FStar_Ident.string_of_lid
                                             modul1.FStar_Syntax_Syntax.name in
                                         FStar_String.lowercase uu____233 in
                                       uu____228 <> uu____232 in
                                     if uu____227
                                     then
                                       Prims.raise
                                         (FStar_Errors.Err
                                            "Interactive mode only supports a single module at the top-level")
                                     else env
                                 | None  -> env in
                               let uu____235 =
                                 FStar_TypeChecker_Tc.tc_partial_modul env1
                                   modul in
                               (match uu____235 with
                                | (modul1,uu____246,env2) ->
                                    Some ((Some modul1), dsenv2, env2))))
                 | FStar_Parser_Driver.Decls ast_decls ->
                     let uu____257 =
                       FStar_Util.fold_map
                         FStar_ToSyntax_Interleave.prefix_with_interface_decls
                         dsenv ast_decls in
                     (match uu____257 with
                      | (dsenv1,ast_decls_l) ->
                          let uu____274 =
                            FStar_ToSyntax_ToSyntax.desugar_decls dsenv1
                              (FStar_List.flatten ast_decls_l) in
                          (match uu____274 with
                           | (dsenv2,decls) ->
                               (match curmod with
                                | None  ->
                                    (FStar_Util.print_error
                                       "fragment without an enclosing module";
                                     FStar_All.exit (Prims.parse_int "1"))
                                | Some modul ->
                                    let uu____296 =
                                      FStar_TypeChecker_Tc.tc_more_partial_modul
                                        env modul decls in
                                    (match uu____296 with
                                     | (modul1,uu____307,env1) ->
                                         Some ((Some modul1), dsenv2, env1)))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____324 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____324 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
               | FStar_Errors.Err msg when
                   let uu____335 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____335 ->
                   (FStar_TypeChecker_Err.add_errors env
                      [(msg, FStar_Range.dummyRange)];
                    None)
               | e when
                   let uu____346 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____346 -> Prims.raise e)
let load_interface_decls:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    FStar_Parser_ParseIt.filename ->
      (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____360  ->
    fun interface_file_name  ->
      match uu____360 with
      | (dsenv,env) ->
          (try
             let r =
               FStar_Parser_ParseIt.parse
                 (FStar_Util.Inl interface_file_name) in
             match r with
             | FStar_Util.Inl
                 (FStar_Util.Inl ((FStar_Parser_AST.Interface
                  (l,decls,uu____389))::[]),uu____390)
                 ->
                 let uu____416 =
                   FStar_ToSyntax_Interleave.initialize_interface l decls
                     dsenv in
                 (uu____416, env)
             | FStar_Util.Inl uu____417 ->
                 let uu____430 =
                   let uu____431 =
                     FStar_Util.format1
                       "Unexpected result from parsing %s; expected a single interface"
                       interface_file_name in
                   FStar_Errors.Err uu____431 in
                 Prims.raise uu____430
             | FStar_Util.Inr (err1,rng) ->
                 Prims.raise (FStar_Errors.Error (err1, rng))
           with
           | FStar_Errors.Error (msg,r) when
               let uu____450 = FStar_Options.trace_error () in
               Prims.op_Negation uu____450 ->
               (FStar_TypeChecker_Err.add_errors env [(msg, r)]; (dsenv, env))
           | FStar_Errors.Err msg when
               let uu____457 = FStar_Options.trace_error () in
               Prims.op_Negation uu____457 ->
               (FStar_TypeChecker_Err.add_errors env
                  [(msg, FStar_Range.dummyRange)];
                (dsenv, env))
           | e when
               let uu____464 = FStar_Options.trace_error () in
               Prims.op_Negation uu____464 -> Prims.raise e)
let tc_one_file:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env ->
      Prims.string Prims.option ->
        Prims.string ->
          ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
            FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun dsenv  ->
    fun env  ->
      fun pre_fn  ->
        fun fn  ->
          let uu____493 = parse dsenv pre_fn fn in
          match uu____493 with
          | (dsenv1,fmods) ->
              let check_mods uu____516 =
                let uu____517 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
                       (fun uu____534  ->
                          fun m  ->
                            match uu____534 with
                            | (env1,all_mods) ->
                                let uu____554 =
                                  FStar_Util.record_time
                                    (fun uu____561  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____554 with
                                 | ((m1,env2),elapsed_ms) ->
                                     (env2, ((m1, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____517 with
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
                   let uu____608 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____608
                     check_mods
               | uu____615 -> check_mods ())
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____625 = FStar_Util.get_file_extension intf in
          uu____625 = "fsti"))
        &&
        (let uu____626 = FStar_Util.get_file_extension impl in
         uu____626 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____634 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____634 Prims.ignore);
      (let uu____636 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____636 Prims.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____645  ->
    fun msg  ->
      match uu____645 with
      | (dsenv,env) ->
          let dsenv1 = FStar_ToSyntax_Env.push dsenv in
          let env1 = FStar_TypeChecker_Env.push env msg in (dsenv1, env1)
let tc_one_file_and_intf:
  Prims.string Prims.option ->
    Prims.string ->
      FStar_ToSyntax_Env.env ->
        FStar_TypeChecker_Env.env ->
          ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
            FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun intf  ->
    fun impl  ->
      fun dsenv  ->
        fun env  ->
          FStar_Syntax_Syntax.reset_gensym ();
          (match intf with
           | None  -> tc_one_file dsenv env None impl
           | Some uu____682 when
               let uu____683 = FStar_Options.codegen () in uu____683 <> None
               ->
               ((let uu____687 =
                   let uu____688 = FStar_Options.lax () in
                   Prims.op_Negation uu____688 in
                 if uu____687
                 then
                   Prims.raise
                     (FStar_Errors.Err
                        "Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")
                 else ());
                tc_one_file dsenv env intf impl)
           | Some iname ->
               ((let uu____692 = FStar_Options.debug_any () in
                 if uu____692
                 then
                   FStar_Util.print1 "Interleaving iface+module: %s\n" iname
                 else ());
                (let caption = Prims.strcat "interface: " iname in
                 let uu____695 = push_context (dsenv, env) caption in
                 match uu____695 with
                 | (dsenv',env') ->
                     let uu____706 = tc_one_file dsenv' env' intf impl in
                     (match uu____706 with
                      | (uu____719,dsenv'1,env'1) ->
                          (pop_context env'1 caption;
                           tc_one_file dsenv env None iname)))))
type uenv = (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
let tc_one_file_from_remaining:
  Prims.string Prims.list ->
    uenv ->
      (Prims.string Prims.list* (FStar_Syntax_Syntax.modul* Prims.int)
        Prims.list* (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env))
  =
  fun remaining  ->
    fun uenv  ->
      let uu____748 = uenv in
      match uu____748 with
      | (dsenv,env) ->
          let uu____760 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____783 =
                  tc_one_file_and_intf (Some intf) impl dsenv env in
                (remaining1, uu____783)
            | intf_or_impl::remaining1 ->
                let uu____800 =
                  tc_one_file_and_intf None intf_or_impl dsenv env in
                (remaining1, uu____800)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____760 with
           | (remaining1,(nmods,dsenv1,env1)) ->
               (remaining1, nmods, (dsenv1, env1)))
let rec tc_fold_interleave:
  ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list* uenv) ->
    Prims.string Prims.list ->
      ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list* uenv)
  =
  fun acc  ->
    fun remaining  ->
      match remaining with
      | [] -> acc
      | uu____887 ->
          let uu____889 = acc in
          (match uu____889 with
           | (mods,uenv) ->
               let uu____908 = tc_one_file_from_remaining remaining uenv in
               (match uu____908 with
                | (remaining1,nmods,(dsenv,env)) ->
                    tc_fold_interleave
                      ((FStar_List.append mods nmods), (dsenv, env))
                      remaining1))
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
        let uu____961 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____961 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____992 =
                (FStar_Options.interactive ()) &&
                  (let uu____993 = FStar_Errors.get_err_count () in
                   uu____993 = (Prims.parse_int "0")) in
              if uu____992
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
    let uu____1009 = tc_prims () in
    match uu____1009 with
    | (prims_mod,dsenv,env) ->
        ((let uu____1029 =
            (let uu____1030 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1030) && (FStar_Options.debug_any ()) in
          if uu____1029
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1033 =
                let uu____1034 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1034 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1033))
          else ());
         (let uu____1037 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____1037 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))