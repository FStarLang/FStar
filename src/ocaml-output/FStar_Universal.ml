open Prims
let module_or_interface_name:
  FStar_Syntax_Syntax.modul -> (Prims.bool* FStar_Ident.lident) =
  fun m  ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
let parse:
  FStar_ToSyntax_Env.env ->
    Prims.string option ->
      Prims.string ->
        (FStar_ToSyntax_Env.env* FStar_Syntax_Syntax.modul Prims.list)
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____27 = FStar_Parser_Driver.parse_file fn in
        match uu____27 with
        | (ast,uu____37) ->
            let uu____44 =
              match pre_fn with
              | None  -> (env, ast)
              | Some pre_fn1 ->
                  let uu____50 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____50 with
                   | (pre_ast,uu____59) ->
                       (match (pre_ast, ast) with
                        | ((FStar_Parser_AST.Interface
                           (lid1,decls1,uu____70))::[],(FStar_Parser_AST.Module
                           (lid2,decls2))::[]) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let env1 =
                              FStar_ToSyntax_Interleave.initialize_interface
                                lid1 decls1 env in
                            let uu____80 =
                              let uu____83 = FStar_List.hd ast in
                              FStar_ToSyntax_Interleave.interleave_module
                                env1 uu____83 true in
                            (match uu____80 with
                             | (env2,ast1) -> (env2, [ast1]))
                        | uu____89 ->
                            raise
                              (FStar_Errors.Err
                                 "mismatch between pre-module and module\n"))) in
            (match uu____44 with
             | (env1,ast1) -> FStar_ToSyntax_ToSyntax.desugar_file env1 ast1)
let tc_prims:
  Prims.unit ->
    ((FStar_Syntax_Syntax.modul* Prims.int)* FStar_ToSyntax_Env.env*
      FStar_TypeChecker_Env.env)
  =
  fun uu____107  ->
    let solver1 =
      let uu____114 = FStar_Options.lax () in
      if uu____114
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___193_116 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___193_116.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___193_116.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___193_116.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___193_116.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___193_116.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___193_116.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___193_116.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___193_116.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___193_116.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___193_116.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___193_116.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___193_116.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Syntax_Const.prims_lid in
    let env1 =
      let uu___194_119 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___194_119.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___194_119.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___194_119.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___194_119.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___194_119.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___194_119.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___194_119.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___194_119.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___194_119.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___194_119.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___194_119.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___194_119.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___194_119.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___194_119.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___194_119.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___194_119.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___194_119.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___194_119.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___194_119.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___194_119.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.type_of =
          (uu___194_119.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___194_119.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___194_119.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___194_119.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___194_119.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth
      } in
    (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env1;
    (let prims_filename = FStar_Options.prims () in
     let uu____122 =
       let uu____126 = FStar_ToSyntax_Env.empty_env () in
       parse uu____126 None prims_filename in
     match uu____122 with
     | (dsenv,prims_mod) ->
         let uu____136 =
           FStar_Util.record_time
             (fun uu____143  ->
                let uu____144 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env1 uu____144) in
         (match uu____136 with
          | ((prims_mod1,env2),elapsed_time) ->
              ((prims_mod1, elapsed_time), dsenv, env2)))
let tc_one_fragment:
  FStar_Syntax_Syntax.modul option ->
    FStar_ToSyntax_Env.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_Parser_ParseIt.input_frag* Prims.bool) ->
          (FStar_Syntax_Syntax.modul option* FStar_ToSyntax_Env.env*
            FStar_TypeChecker_Env.env) option
  =
  fun curmod  ->
    fun dsenv  ->
      fun env  ->
        fun uu____180  ->
          match uu____180 with
          | (frag,is_interface_dependence) ->
              (try
                 let uu____202 = FStar_Parser_Driver.parse_fragment frag in
                 match uu____202 with
                 | FStar_Parser_Driver.Empty  -> Some (curmod, dsenv, env)
                 | FStar_Parser_Driver.Modul ast_modul ->
                     let uu____214 =
                       FStar_ToSyntax_Interleave.interleave_module dsenv
                         ast_modul false in
                     (match uu____214 with
                      | (ds_env,ast_modul1) ->
                          let uu____224 =
                            FStar_ToSyntax_ToSyntax.desugar_partial_modul
                              curmod dsenv ast_modul1 in
                          (match uu____224 with
                           | (dsenv1,modul) ->
                               let dsenv2 =
                                 if is_interface_dependence
                                 then
                                   FStar_ToSyntax_Env.set_iface dsenv1 false
                                 else dsenv1 in
                               let env1 =
                                 match curmod with
                                 | Some modul1 ->
                                     let uu____238 =
                                       let uu____239 =
                                         let uu____240 =
                                           let uu____241 =
                                             FStar_Options.file_list () in
                                           FStar_List.hd uu____241 in
                                         FStar_Parser_Dep.lowercase_module_name
                                           uu____240 in
                                       let uu____243 =
                                         let uu____244 =
                                           FStar_Ident.string_of_lid
                                             modul1.FStar_Syntax_Syntax.name in
                                         FStar_String.lowercase uu____244 in
                                       uu____239 <> uu____243 in
                                     if uu____238
                                     then
                                       raise
                                         (FStar_Errors.Err
                                            "Interactive mode only supports a single module at the top-level")
                                     else env
                                 | None  -> env in
                               let uu____246 =
                                 let uu____251 =
                                   FStar_ToSyntax_Env.syntax_only dsenv2 in
                                 if uu____251
                                 then (modul, [], env1)
                                 else
                                   FStar_TypeChecker_Tc.tc_partial_modul env1
                                     modul in
                               (match uu____246 with
                                | (modul1,uu____264,env2) ->
                                    Some ((Some modul1), dsenv2, env2))))
                 | FStar_Parser_Driver.Decls ast_decls ->
                     let uu____275 =
                       FStar_Util.fold_map
                         FStar_ToSyntax_Interleave.prefix_with_interface_decls
                         dsenv ast_decls in
                     (match uu____275 with
                      | (dsenv1,ast_decls_l) ->
                          let uu____292 =
                            FStar_ToSyntax_ToSyntax.desugar_decls dsenv1
                              (FStar_List.flatten ast_decls_l) in
                          (match uu____292 with
                           | (dsenv2,decls) ->
                               (match curmod with
                                | None  ->
                                    (FStar_Util.print_error
                                       "fragment without an enclosing module";
                                     FStar_All.exit (Prims.parse_int "1"))
                                | Some modul ->
                                    let uu____314 =
                                      let uu____319 =
                                        FStar_ToSyntax_Env.syntax_only dsenv2 in
                                      if uu____319
                                      then (modul, [], env)
                                      else
                                        FStar_TypeChecker_Tc.tc_more_partial_modul
                                          env modul decls in
                                    (match uu____314 with
                                     | (modul1,uu____332,env1) ->
                                         Some ((Some modul1), dsenv2, env1)))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____349 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____349 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
               | FStar_Errors.Err msg when
                   let uu____360 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____360 ->
                   (FStar_TypeChecker_Err.add_errors env
                      [(msg, FStar_Range.dummyRange)];
                    None)
               | e when
                   let uu____371 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____371 -> raise e)
let load_interface_decls:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    FStar_Parser_ParseIt.filename ->
      (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____387  ->
    fun interface_file_name  ->
      match uu____387 with
      | (dsenv,env) ->
          (try
             let r =
               FStar_Parser_ParseIt.parse
                 (FStar_Util.Inl interface_file_name) in
             match r with
             | FStar_Util.Inl
                 (FStar_Util.Inl ((FStar_Parser_AST.Interface
                  (l,decls,uu____416))::[]),uu____417)
                 ->
                 let uu____443 =
                   FStar_ToSyntax_Interleave.initialize_interface l decls
                     dsenv in
                 (uu____443, env)
             | FStar_Util.Inl uu____444 ->
                 let uu____457 =
                   let uu____458 =
                     FStar_Util.format1
                       "Unexpected result from parsing %s; expected a single interface"
                       interface_file_name in
                   FStar_Errors.Err uu____458 in
                 raise uu____457
             | FStar_Util.Inr (err1,rng) ->
                 raise (FStar_Errors.Error (err1, rng))
           with
           | FStar_Errors.Error (msg,r) when
               let uu____477 = FStar_Options.trace_error () in
               Prims.op_Negation uu____477 ->
               (FStar_TypeChecker_Err.add_errors env [(msg, r)]; (dsenv, env))
           | FStar_Errors.Err msg when
               let uu____484 = FStar_Options.trace_error () in
               Prims.op_Negation uu____484 ->
               (FStar_TypeChecker_Err.add_errors env
                  [(msg, FStar_Range.dummyRange)];
                (dsenv, env))
           | e when
               let uu____491 = FStar_Options.trace_error () in
               Prims.op_Negation uu____491 -> raise e)
let tc_one_file:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env ->
      Prims.string option ->
        Prims.string ->
          ((FStar_Syntax_Syntax.modul* Prims.int) Prims.list*
            FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun dsenv  ->
    fun env  ->
      fun pre_fn  ->
        fun fn  ->
          let uu____524 = parse dsenv pre_fn fn in
          match uu____524 with
          | (dsenv1,fmods) ->
              let check_mods uu____547 =
                let uu____548 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
                       (fun uu____565  ->
                          fun m  ->
                            match uu____565 with
                            | (env1,all_mods) ->
                                let uu____585 =
                                  FStar_Util.record_time
                                    (fun uu____592  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____585 with
                                 | ((m1,env2),elapsed_ms) ->
                                     (env2, ((m1, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____548 with
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
                   let uu____639 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____639
                     check_mods
               | uu____646 -> check_mods ())
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____658 = FStar_Util.get_file_extension intf in
          uu____658 = "fsti"))
        &&
        (let uu____659 = FStar_Util.get_file_extension impl in
         uu____659 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____669 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____669 FStar_Pervasives.ignore);
      (let uu____671 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____671 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____682  ->
    fun msg  ->
      match uu____682 with
      | (dsenv,env) ->
          let dsenv1 = FStar_ToSyntax_Env.push dsenv in
          let env1 = FStar_TypeChecker_Env.push env msg in (dsenv1, env1)
type uenv = (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
let tc_one_file_from_remaining:
  Prims.string Prims.list ->
    uenv ->
      (Prims.string Prims.list* (FStar_Syntax_Syntax.modul* Prims.int)
        Prims.list* (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env))
  =
  fun remaining  ->
    fun uenv  ->
      let uu____713 = uenv in
      match uu____713 with
      | (dsenv,env) ->
          let uu____725 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____748 = tc_one_file dsenv env (Some intf) impl in
                (remaining1, uu____748)
            | intf_or_impl::remaining1 ->
                let uu____765 = tc_one_file dsenv env None intf_or_impl in
                (remaining1, uu____765)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____725 with
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
      | uu____854 ->
          let uu____856 = acc in
          (match uu____856 with
           | (mods,uenv) ->
               let uu____875 = tc_one_file_from_remaining remaining uenv in
               (match uu____875 with
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
        let uu____931 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____931 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____962 =
                (FStar_Options.interactive ()) &&
                  (let uu____963 = FStar_Errors.get_err_count () in
                   uu____963 = (Prims.parse_int "0")) in
              if uu____962
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
    let uu____980 = tc_prims () in
    match uu____980 with
    | (prims_mod,dsenv,env) ->
        ((let uu____1000 =
            (let uu____1001 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1001) && (FStar_Options.debug_any ()) in
          if uu____1000
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1004 =
                let uu____1005 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1005 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1004))
          else ());
         (let uu____1008 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____1008 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))