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
        (FStar_Parser_ParseIt.input_frag* Prims.bool) ->
          (FStar_Syntax_Syntax.modul Prims.option* FStar_ToSyntax_Env.env*
            FStar_TypeChecker_Env.env) Prims.option
  =
  fun curmod  ->
    fun dsenv  ->
      fun env  ->
        fun uu____152  ->
          match uu____152 with
          | (frag,is_interface_dependence) ->
              (try
                 let uu____174 = FStar_Parser_Driver.parse_fragment frag in
                 match uu____174 with
                 | FStar_Parser_Driver.Empty  -> Some (curmod, dsenv, env)
                 | FStar_Parser_Driver.Modul ast_modul ->
                     let ast_modul1 =
                       if is_interface_dependence
                       then FStar_ToSyntax_ToSyntax.as_interface ast_modul
                       else ast_modul in
                     let uu____188 =
                       FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod
                         dsenv ast_modul1 in
                     (match uu____188 with
                      | (dsenv1,modul) ->
                          let dsenv2 =
                            if is_interface_dependence
                            then FStar_ToSyntax_Env.set_iface dsenv1 false
                            else dsenv1 in
                          let env1 =
                            match curmod with
                            | Some modul1 ->
                                let uu____202 =
                                  let uu____203 =
                                    let uu____204 =
                                      let uu____205 =
                                        FStar_Options.file_list () in
                                      FStar_List.hd uu____205 in
                                    FStar_Parser_Dep.lowercase_module_name
                                      uu____204 in
                                  let uu____207 =
                                    let uu____208 =
                                      FStar_Ident.string_of_lid
                                        modul1.FStar_Syntax_Syntax.name in
                                    FStar_String.lowercase uu____208 in
                                  uu____203 <> uu____207 in
                                if uu____202
                                then
                                  Prims.raise
                                    (FStar_Errors.Err
                                       "Interactive mode only supports a single module at the top-level")
                                else env
                            | None  -> env in
                          let uu____210 =
                            FStar_TypeChecker_Tc.tc_partial_modul env1 modul in
                          (match uu____210 with
                           | (modul1,uu____221,env2) ->
                               Some ((Some modul1), dsenv2, env2)))
                 | FStar_Parser_Driver.Decls ast_decls ->
                     let uu____232 =
                       FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls in
                     (match uu____232 with
                      | (dsenv1,decls) ->
                          (match curmod with
                           | None  ->
                               (FStar_Util.print_error
                                  "fragment without an enclosing module";
                                FStar_All.exit (Prims.parse_int "1"))
                           | Some modul ->
                               let uu____254 =
                                 FStar_TypeChecker_Tc.tc_more_partial_modul
                                   env modul decls in
                               (match uu____254 with
                                | (modul1,uu____265,env1) ->
                                    Some ((Some modul1), dsenv1, env1))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____282 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____282 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
               | FStar_Errors.Err msg when
                   let uu____293 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____293 ->
                   (FStar_TypeChecker_Err.add_errors env
                      [(msg, FStar_Range.dummyRange)];
                    None)
               | e when
                   let uu____304 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____304 -> Prims.raise e)
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
          let uu____336 = parse dsenv pre_fn fn in
          match uu____336 with
          | (dsenv1,fmods) ->
              let check_mods uu____359 =
                let uu____360 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
                       (fun uu____377  ->
                          fun m  ->
                            match uu____377 with
                            | (env1,all_mods) ->
                                let uu____397 =
                                  FStar_Util.record_time
                                    (fun uu____404  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____397 with
                                 | ((m1,env2),elapsed_ms) ->
                                     (env2, ((m1, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____360 with
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
                   let uu____451 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____451
                     check_mods
               | uu____458 -> check_mods ())
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____468 = FStar_Util.get_file_extension intf in
          uu____468 = "fsti"))
        &&
        (let uu____469 = FStar_Util.get_file_extension impl in
         uu____469 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____477 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____477 Prims.ignore);
      (let uu____479 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____479 Prims.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____488  ->
    fun msg  ->
      match uu____488 with
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
           | Some uu____525 when
               let uu____526 = FStar_Options.codegen () in uu____526 <> None
               ->
               ((let uu____530 =
                   let uu____531 = FStar_Options.lax () in
                   Prims.op_Negation uu____531 in
                 if uu____530
                 then
                   Prims.raise
                     (FStar_Errors.Err
                        "Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")
                 else ());
                tc_one_file dsenv env intf impl)
           | Some iname ->
               ((let uu____535 = FStar_Options.debug_any () in
                 if uu____535
                 then
                   FStar_Util.print1 "Interleaving iface+module: %s\n" iname
                 else ());
                (let caption = Prims.strcat "interface: " iname in
                 let uu____538 = push_context (dsenv, env) caption in
                 match uu____538 with
                 | (dsenv',env') ->
                     let uu____549 = tc_one_file dsenv' env' intf impl in
                     (match uu____549 with
                      | (uu____562,dsenv'1,env'1) ->
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
      let uu____591 = uenv in
      match uu____591 with
      | (dsenv,env) ->
          let uu____603 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____626 =
                  tc_one_file_and_intf (Some intf) impl dsenv env in
                (remaining1, uu____626)
            | intf_or_impl::remaining1 ->
                let uu____643 =
                  tc_one_file_and_intf None intf_or_impl dsenv env in
                (remaining1, uu____643)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____603 with
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
      | uu____730 ->
          let uu____732 = acc in
          (match uu____732 with
           | (mods,uenv) ->
               let uu____751 = tc_one_file_from_remaining remaining uenv in
               (match uu____751 with
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
        let uu____804 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____804 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____835 =
                (FStar_Options.interactive ()) &&
                  (let uu____836 = FStar_Errors.get_err_count () in
                   uu____836 = (Prims.parse_int "0")) in
              if uu____835
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
    let uu____852 = tc_prims () in
    match uu____852 with
    | (prims_mod,dsenv,env) ->
        ((let uu____872 =
            (let uu____873 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____873) && (FStar_Options.debug_any ()) in
          if uu____872
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____876 =
                let uu____877 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____877 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____876))
          else ());
         (let uu____880 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____880 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))