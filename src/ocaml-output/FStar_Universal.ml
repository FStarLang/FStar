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
            let ast =
              match pre_fn with
              | None  -> ast
              | Some pre_fn ->
                  let uu____42 = FStar_Parser_Driver.parse_file pre_fn in
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
            FStar_ToSyntax_ToSyntax.desugar_file env ast
let tc_prims:
  Prims.unit ->
    ((FStar_Syntax_Syntax.modul* Prims.int)* FStar_ToSyntax_Env.env*
      FStar_TypeChecker_Env.env)
  =
  fun uu____85  ->
    let solver =
      let uu____92 = FStar_Options.lax () in
      if uu____92
      then FStar_SMTEncoding_Solver.dummy
      else FStar_SMTEncoding_Solver.solver in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver
        FStar_Syntax_Const.prims_lid in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let prims_filename = FStar_Options.prims () in
     let uu____97 =
       let uu____101 = FStar_ToSyntax_Env.empty_env () in
       parse uu____101 None prims_filename in
     match uu____97 with
     | (dsenv,prims_mod) ->
         let uu____111 =
           FStar_Util.record_time
             (fun uu____118  ->
                let uu____119 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env uu____119) in
         (match uu____111 with
          | ((prims_mod,env),elapsed_time) ->
              ((prims_mod, elapsed_time), dsenv, env)))
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
            let uu____162 = FStar_Parser_Driver.parse_fragment frag in
            match uu____162 with
            | FStar_Parser_Driver.Empty  -> Some (curmod, dsenv, env)
            | FStar_Parser_Driver.Modul ast_modul ->
                let uu____174 =
                  FStar_ToSyntax_ToSyntax.desugar_partial_modul curmod dsenv
                    ast_modul in
                (match uu____174 with
                 | (dsenv,modul) ->
                     let env =
                       match curmod with
                       | Some modul ->
                           let uu____186 =
                             let uu____187 =
                               let uu____188 =
                                 let uu____189 = FStar_Options.file_list () in
                                 FStar_List.hd uu____189 in
                               FStar_Parser_Dep.lowercase_module_name
                                 uu____188 in
                             let uu____191 =
                               let uu____192 =
                                 FStar_Ident.string_of_lid
                                   modul.FStar_Syntax_Syntax.name in
                               FStar_String.lowercase uu____192 in
                             uu____187 <> uu____191 in
                           if uu____186
                           then
                             Prims.raise
                               (FStar_Errors.Err
                                  "Interactive mode only supports a single module at the top-level")
                           else env
                       | None  -> env in
                     let uu____194 =
                       FStar_TypeChecker_Tc.tc_partial_modul env modul in
                     (match uu____194 with
                      | (modul,uu____205,env) ->
                          Some ((Some modul), dsenv, env)))
            | FStar_Parser_Driver.Decls ast_decls ->
                let uu____216 =
                  FStar_ToSyntax_ToSyntax.desugar_decls dsenv ast_decls in
                (match uu____216 with
                 | (dsenv,decls) ->
                     (match curmod with
                      | None  ->
                          (FStar_Util.print_error
                             "fragment without an enclosing module";
                           FStar_All.exit (Prims.parse_int "1"))
                      | Some modul ->
                          let uu____238 =
                            FStar_TypeChecker_Tc.tc_more_partial_modul env
                              modul decls in
                          (match uu____238 with
                           | (modul,uu____249,env) ->
                               Some ((Some modul), dsenv, env))))
          with
          | FStar_Errors.Error (msg,r) when
              let uu____266 = FStar_Options.trace_error () in
              Prims.op_Negation uu____266 ->
              (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
          | FStar_Errors.Err msg when
              let uu____277 = FStar_Options.trace_error () in
              Prims.op_Negation uu____277 ->
              (FStar_TypeChecker_Err.add_errors env
                 [(msg, FStar_Range.dummyRange)];
               None)
          | e when
              let uu____288 = FStar_Options.trace_error () in
              Prims.op_Negation uu____288 -> Prims.raise e
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
          let uu____320 = parse dsenv pre_fn fn in
          match uu____320 with
          | (dsenv,fmods) ->
              let check_mods uu____343 =
                let uu____344 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
                       (fun uu____361  ->
                          fun m  ->
                            match uu____361 with
                            | (env,all_mods) ->
                                let uu____381 =
                                  FStar_Util.record_time
                                    (fun uu____388  ->
                                       FStar_TypeChecker_Tc.check_module env
                                         m) in
                                (match uu____381 with
                                 | ((m,env),elapsed_ms) ->
                                     (env, ((m, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____344 with
                | (env,all_mods) -> ((FStar_List.rev all_mods), dsenv, env) in
              (match fmods with
               | m::[] when
                   (FStar_Options.should_verify
                      (m.FStar_Syntax_Syntax.name).FStar_Ident.str)
                     &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ()))
                   ->
                   let uu____435 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____435
                     check_mods
               | uu____442 -> check_mods ())
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____452 = FStar_Util.get_file_extension intf in
          uu____452 = "fsti"))
        &&
        (let uu____453 = FStar_Util.get_file_extension impl in
         uu____453 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____461 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____461 Prims.ignore);
      (let uu____463 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____463 Prims.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____472  ->
    fun msg  ->
      match uu____472 with
      | (dsenv,env) ->
          let dsenv = FStar_ToSyntax_Env.push dsenv in
          let env = FStar_TypeChecker_Env.push env msg in (dsenv, env)
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
           | Some uu____509 when
               let uu____510 = FStar_Options.codegen () in uu____510 <> None
               ->
               ((let uu____514 =
                   let uu____515 = FStar_Options.lax () in
                   Prims.op_Negation uu____515 in
                 if uu____514
                 then
                   Prims.raise
                     (FStar_Errors.Err
                        "Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately")
                 else ());
                tc_one_file dsenv env intf impl)
           | Some iname ->
               ((let uu____519 = FStar_Options.debug_any () in
                 if uu____519
                 then
                   FStar_Util.print1 "Interleaving iface+module: %s\n" iname
                 else ());
                (let caption = Prims.strcat "interface: " iname in
                 let uu____522 = push_context (dsenv, env) caption in
                 match uu____522 with
                 | (dsenv',env') ->
                     let uu____533 = tc_one_file dsenv' env' intf impl in
                     (match uu____533 with
                      | (uu____546,dsenv',env') ->
                          (pop_context env' caption;
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
      let uu____575 = uenv in
      match uu____575 with
      | (dsenv,env) ->
          let uu____587 =
            match remaining with
            | intf::impl::remaining when needs_interleaving intf impl ->
                let uu____610 =
                  tc_one_file_and_intf (Some intf) impl dsenv env in
                (remaining, uu____610)
            | intf_or_impl::remaining ->
                let uu____627 =
                  tc_one_file_and_intf None intf_or_impl dsenv env in
                (remaining, uu____627)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____587 with
           | (remaining,(nmods,dsenv,env)) ->
               (remaining, nmods, (dsenv, env)))
let rec tc_fold_interleave:
  ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list* uenv) ->
    Prims.string Prims.list ->
      ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list* uenv)
  =
  fun acc  ->
    fun remaining  ->
      match remaining with
      | [] -> acc
      | uu____714 ->
          let uu____716 = acc in
          (match uu____716 with
           | (mods,uenv) ->
               let uu____735 = tc_one_file_from_remaining remaining uenv in
               (match uu____735 with
                | (remaining,nmods,(dsenv,env)) ->
                    tc_fold_interleave
                      ((FStar_List.append mods nmods), (dsenv, env))
                      remaining))
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
        let uu____788 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____788 with
        | (all_mods,(dsenv,env)) ->
            ((let uu____819 =
                (FStar_Options.interactive ()) &&
                  (let uu____820 = FStar_Errors.get_err_count () in
                   uu____820 = (Prims.parse_int "0")) in
              if uu____819
              then
                (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                  ()
              else
                (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                  ());
             (all_mods, dsenv, env))
let batch_mode_tc:
  Prims.string Prims.list ->
    ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
      FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun filenames  ->
    let uu____836 = tc_prims () in
    match uu____836 with
    | (prims_mod,dsenv,env) ->
        ((let uu____856 =
            (let uu____857 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____857) && (FStar_Options.debug_any ()) in
          if uu____856
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____860 =
                let uu____861 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____861 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____860))
          else ());
         (let uu____864 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____864 with
          | (all_mods,dsenv,env) -> ((prims_mod :: all_mods), dsenv, env)))