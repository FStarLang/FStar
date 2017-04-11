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
        (let uu___214_94 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___214_94.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___214_94.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___214_94.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___214_94.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___214_94.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___214_94.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___214_94.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___214_94.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___214_94.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___214_94.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___214_94.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___214_94.FStar_TypeChecker_Env.refresh)
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
          ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
            FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun dsenv  ->
    fun env  ->
      fun pre_fn  ->
        fun fn  ->
          let uu____321 = parse dsenv pre_fn fn in
          match uu____321 with
          | (dsenv1,fmods) ->
              let check_mods uu____344 =
                let uu____345 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
                       (fun uu____362  ->
                          fun m  ->
                            match uu____362 with
                            | (env1,all_mods) ->
                                let uu____382 =
                                  FStar_Util.record_time
                                    (fun uu____389  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____382 with
                                 | ((m1,env2),elapsed_ms) ->
                                     (env2, ((m1, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____345 with
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
                   let uu____436 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____436
                     check_mods
               | uu____443 -> check_mods ())
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____453 = FStar_Util.get_file_extension intf in
          uu____453 = "fsti"))
        &&
        (let uu____454 = FStar_Util.get_file_extension impl in
         uu____454 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____462 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____462 Prims.ignore);
      (let uu____464 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____464 Prims.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____473  ->
    fun msg  ->
      match uu____473 with
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
           | Some uu____510 when
               let uu____511 = FStar_Options.codegen () in uu____511 <> None
               ->
               ((let uu____515 =
                   let uu____516 = FStar_Options.lax () in
                   Prims.op_Negation uu____516 in
                 if uu____515
                 then
                   Prims.raise
                     (FStar_Errors.Err
                        "Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")
                 else ());
                tc_one_file dsenv env intf impl)
           | Some iname ->
               ((let uu____520 = FStar_Options.debug_any () in
                 if uu____520
                 then
                   FStar_Util.print1 "Interleaving iface+module: %s\n" iname
                 else ());
                (let caption = Prims.strcat "interface: " iname in
                 let uu____523 = push_context (dsenv, env) caption in
                 match uu____523 with
                 | (dsenv',env') ->
                     let uu____534 = tc_one_file dsenv' env' intf impl in
                     (match uu____534 with
                      | (uu____547,dsenv'1,env'1) ->
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
      let uu____576 = uenv in
      match uu____576 with
      | (dsenv,env) ->
          let uu____588 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____611 =
                  tc_one_file_and_intf (Some intf) impl dsenv env in
                (remaining1, uu____611)
            | intf_or_impl::remaining1 ->
                let uu____628 =
                  tc_one_file_and_intf None intf_or_impl dsenv env in
                (remaining1, uu____628)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____588 with
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
      | uu____715 ->
          let uu____717 = acc in
          (match uu____717 with
           | (mods,uenv) ->
               let uu____736 = tc_one_file_from_remaining remaining uenv in
               (match uu____736 with
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
        let uu____789 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____789 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____820 =
                (FStar_Options.interactive ()) &&
                  (let uu____821 = FStar_Errors.get_err_count () in
                   uu____821 = (Prims.parse_int "0")) in
              if uu____820
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
    let uu____837 = tc_prims () in
    match uu____837 with
    | (prims_mod,dsenv,env) ->
        ((let uu____857 =
            (let uu____858 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____858) && (FStar_Options.debug_any ()) in
          if uu____857
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____861 =
                let uu____862 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____862 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____861))
          else ());
         (let uu____865 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____865 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))