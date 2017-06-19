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
                            raise
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
        (let uu___222_111 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___222_111.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___222_111.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___222_111.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___222_111.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___222_111.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___222_111.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___222_111.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___222_111.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___222_111.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___222_111.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___222_111.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___222_111.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Syntax_Const.prims_lid in
    let env1 =
      let uu___223_114 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___223_114.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___223_114.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___223_114.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___223_114.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___223_114.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___223_114.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___223_114.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___223_114.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___223_114.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___223_114.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___223_114.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___223_114.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___223_114.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___223_114.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___223_114.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___223_114.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___223_114.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___223_114.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___223_114.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___223_114.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.type_of =
          (uu___223_114.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___223_114.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___223_114.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___223_114.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___223_114.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___223_114.FStar_TypeChecker_Env.is_native_tactic)
      } in
    let env2 =
      let uu___224_116 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___224_116.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___224_116.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___224_116.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___224_116.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___224_116.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___224_116.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___224_116.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___224_116.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___224_116.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___224_116.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___224_116.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___224_116.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___224_116.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___224_116.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___224_116.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___224_116.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___224_116.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___224_116.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___224_116.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___224_116.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.type_of =
          (uu___224_116.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___224_116.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___224_116.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___224_116.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___224_116.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___224_116.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic
      } in
    (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env2;
    (let prims_filename = FStar_Options.prims () in
     let uu____119 =
       let uu____123 = FStar_ToSyntax_Env.empty_env () in
       parse uu____123 None prims_filename in
     match uu____119 with
     | (dsenv,prims_mod) ->
         let uu____133 =
           FStar_Util.record_time
             (fun uu____140  ->
                let uu____141 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env2 uu____141) in
         (match uu____133 with
          | ((prims_mod1,env3),elapsed_time) ->
              ((prims_mod1, elapsed_time), dsenv, env3)))
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
        fun uu____173  ->
          match uu____173 with
          | (frag,is_interface_dependence) ->
              (try
                 let uu____195 = FStar_Parser_Driver.parse_fragment frag in
                 match uu____195 with
                 | FStar_Parser_Driver.Empty  -> Some (curmod, dsenv, env)
                 | FStar_Parser_Driver.Modul ast_modul ->
                     let uu____207 =
                       FStar_ToSyntax_Interleave.interleave_module dsenv
                         ast_modul false in
                     (match uu____207 with
                      | (ds_env,ast_modul1) ->
                          let uu____217 =
                            FStar_ToSyntax_ToSyntax.desugar_partial_modul
                              curmod dsenv ast_modul1 in
                          (match uu____217 with
                           | (dsenv1,modul) ->
                               let dsenv2 =
                                 if is_interface_dependence
                                 then
                                   FStar_ToSyntax_Env.set_iface dsenv1 false
                                 else dsenv1 in
                               let env1 =
                                 match curmod with
                                 | Some modul1 ->
                                     let uu____231 =
                                       let uu____232 =
                                         let uu____233 =
                                           let uu____234 =
                                             FStar_Options.file_list () in
                                           FStar_List.hd uu____234 in
                                         FStar_Parser_Dep.lowercase_module_name
                                           uu____233 in
                                       let uu____236 =
                                         let uu____237 =
                                           FStar_Ident.string_of_lid
                                             modul1.FStar_Syntax_Syntax.name in
                                         FStar_String.lowercase uu____237 in
                                       uu____232 <> uu____236 in
                                     if uu____231
                                     then
                                       raise
                                         (FStar_Errors.Err
                                            "Interactive mode only supports a single module at the top-level")
                                     else env
                                 | None  -> env in
                               let uu____239 =
                                 let uu____244 =
                                   FStar_ToSyntax_Env.syntax_only dsenv2 in
                                 if uu____244
                                 then (modul, [], env1)
                                 else
                                   FStar_TypeChecker_Tc.tc_partial_modul env1
                                     modul in
                               (match uu____239 with
                                | (modul1,uu____257,env2) ->
                                    Some ((Some modul1), dsenv2, env2))))
                 | FStar_Parser_Driver.Decls ast_decls ->
                     let uu____268 =
                       FStar_Util.fold_map
                         FStar_ToSyntax_Interleave.prefix_with_interface_decls
                         dsenv ast_decls in
                     (match uu____268 with
                      | (dsenv1,ast_decls_l) ->
                          let uu____285 =
                            FStar_ToSyntax_ToSyntax.desugar_decls dsenv1
                              (FStar_List.flatten ast_decls_l) in
                          (match uu____285 with
                           | (dsenv2,decls) ->
                               (match curmod with
                                | None  ->
                                    (FStar_Util.print_error
                                       "fragment without an enclosing module";
                                     FStar_All.exit (Prims.parse_int "1"))
                                | Some modul ->
                                    let uu____307 =
                                      let uu____312 =
                                        FStar_ToSyntax_Env.syntax_only dsenv2 in
                                      if uu____312
                                      then (modul, [], env)
                                      else
                                        FStar_TypeChecker_Tc.tc_more_partial_modul
                                          env modul decls in
                                    (match uu____307 with
                                     | (modul1,uu____325,env1) ->
                                         Some ((Some modul1), dsenv2, env1)))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____342 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____342 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
               | FStar_Errors.Err msg when
                   let uu____353 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____353 ->
                   (FStar_TypeChecker_Err.add_errors env
                      [(msg, FStar_Range.dummyRange)];
                    None)
               | e when
                   let uu____364 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____364 -> raise e)
let load_interface_decls:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    FStar_Parser_ParseIt.filename ->
      (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____378  ->
    fun interface_file_name  ->
      match uu____378 with
      | (dsenv,env) ->
          (try
             let r =
               FStar_Parser_ParseIt.parse
                 (FStar_Util.Inl interface_file_name) in
             match r with
             | FStar_Util.Inl
                 (FStar_Util.Inl ((FStar_Parser_AST.Interface
                  (l,decls,uu____407))::[]),uu____408)
                 ->
                 let uu____434 =
                   FStar_ToSyntax_Interleave.initialize_interface l decls
                     dsenv in
                 (uu____434, env)
             | FStar_Util.Inl uu____435 ->
                 let uu____448 =
                   let uu____449 =
                     FStar_Util.format1
                       "Unexpected result from parsing %s; expected a single interface"
                       interface_file_name in
                   FStar_Errors.Err uu____449 in
                 raise uu____448
             | FStar_Util.Inr (err1,rng) ->
                 raise (FStar_Errors.Error (err1, rng))
           with
           | FStar_Errors.Error (msg,r) when
               let uu____468 = FStar_Options.trace_error () in
               Prims.op_Negation uu____468 ->
               (FStar_TypeChecker_Err.add_errors env [(msg, r)]; (dsenv, env))
           | FStar_Errors.Err msg when
               let uu____475 = FStar_Options.trace_error () in
               Prims.op_Negation uu____475 ->
               (FStar_TypeChecker_Err.add_errors env
                  [(msg, FStar_Range.dummyRange)];
                (dsenv, env))
           | e when
               let uu____482 = FStar_Options.trace_error () in
               Prims.op_Negation uu____482 -> raise e)
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
          let uu____511 = parse dsenv pre_fn fn in
          match uu____511 with
          | (dsenv1,fmods) ->
              let check_mods uu____534 =
                let uu____535 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
                       (fun uu____552  ->
                          fun m  ->
                            match uu____552 with
                            | (env1,all_mods) ->
                                let uu____572 =
                                  FStar_Util.record_time
                                    (fun uu____579  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____572 with
                                 | ((m1,env2),elapsed_ms) ->
                                     (env2, ((m1, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____535 with
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
                   let uu____626 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____626
                     check_mods
               | uu____633 -> check_mods ())
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____643 = FStar_Util.get_file_extension intf in
          uu____643 = "fsti"))
        &&
        (let uu____644 = FStar_Util.get_file_extension impl in
         uu____644 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____652 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____652 FStar_Pervasives.ignore);
      (let uu____654 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____654 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
  fun uu____663  ->
    fun msg  ->
      match uu____663 with
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
      let uu____692 = uenv in
      match uu____692 with
      | (dsenv,env) ->
          let uu____704 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____727 = tc_one_file dsenv env (Some intf) impl in
                (remaining1, uu____727)
            | intf_or_impl::remaining1 ->
                let uu____744 = tc_one_file dsenv env None intf_or_impl in
                (remaining1, uu____744)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____704 with
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
      | uu____831 ->
          let uu____833 = acc in
          (match uu____833 with
           | (mods,uenv) ->
               let uu____852 = tc_one_file_from_remaining remaining uenv in
               (match uu____852 with
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
        let uu____905 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____905 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____936 =
                (FStar_Options.interactive ()) &&
                  (let uu____937 = FStar_Errors.get_err_count () in
                   uu____937 = (Prims.parse_int "0")) in
              if uu____936
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
    let uu____953 = tc_prims () in
    match uu____953 with
    | (prims_mod,dsenv,env) ->
        ((let uu____973 =
            (let uu____974 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____974) && (FStar_Options.debug_any ()) in
          if uu____973
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____977 =
                let uu____978 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____978 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____977))
          else ());
         (let uu____981 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____981 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))