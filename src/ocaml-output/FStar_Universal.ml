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
        (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pre_fn  ->
      fun fn  ->
        let uu____33 = FStar_Parser_Driver.parse_file fn in
        match uu____33 with
        | (ast,uu____49) ->
            let uu____62 =
              match pre_fn with
              | FStar_Pervasives_Native.None  -> (env, ast)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu____72 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu____72 with
                   | (pre_ast,uu____88) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface
                           (lid1,decls1,uu____107),FStar_Parser_AST.Module
                           (lid2,decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let env1 =
                              FStar_ToSyntax_Interleave.initialize_interface
                                lid1 decls1 env in
                            let uu____119 =
                              FStar_ToSyntax_Interleave.interleave_module
                                env1 ast true in
                            (match uu____119 with
                             | (env2,ast1) -> (env2, ast1))
                        | uu____130 ->
                            FStar_Exn.raise
                              (FStar_Errors.Err
                                 "mismatch between pre-module and module\n"))) in
            (match uu____62 with
             | (env1,ast1) -> FStar_ToSyntax_ToSyntax.desugar_modul env1 ast1)
let tc_prims:
  Prims.unit ->
    ((FStar_Syntax_Syntax.modul,Prims.int) FStar_Pervasives_Native.tuple2,
      FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple3
  =
  fun uu____158  ->
    let solver1 =
      let uu____170 = FStar_Options.lax () in
      if uu____170
      then FStar_SMTEncoding_Solver.dummy
      else
        (let uu___186_172 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___186_172.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___186_172.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___186_172.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___186_172.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___186_172.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___186_172.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___186_172.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___186_172.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___186_172.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___186_172.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___186_172.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___186_172.FStar_TypeChecker_Env.refresh)
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Parser_Const.prims_lid in
    let env1 =
      let uu___187_175 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___187_175.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___187_175.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___187_175.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___187_175.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___187_175.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___187_175.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___187_175.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___187_175.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___187_175.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___187_175.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___187_175.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___187_175.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___187_175.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___187_175.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___187_175.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___187_175.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___187_175.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___187_175.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___187_175.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___187_175.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___187_175.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.type_of =
          (uu___187_175.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___187_175.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___187_175.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___187_175.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___187_175.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___187_175.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___187_175.FStar_TypeChecker_Env.identifier_info)
      } in
    let env2 =
      let uu___188_177 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___188_177.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___188_177.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___188_177.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___188_177.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___188_177.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___188_177.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___188_177.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___188_177.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___188_177.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___188_177.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___188_177.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___188_177.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___188_177.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___188_177.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___188_177.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___188_177.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___188_177.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___188_177.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___188_177.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___188_177.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___188_177.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.type_of =
          (uu___188_177.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___188_177.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___188_177.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___188_177.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___188_177.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___188_177.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic;
        FStar_TypeChecker_Env.identifier_info =
          (uu___188_177.FStar_TypeChecker_Env.identifier_info)
      } in
    (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env2;
    (let prims_filename = FStar_Options.prims () in
     let uu____180 =
       let uu____185 = FStar_ToSyntax_Env.empty_env () in
       parse uu____185 FStar_Pervasives_Native.None prims_filename in
     match uu____180 with
     | (dsenv,prims_mod) ->
         let uu____198 =
           FStar_Util.record_time
             (fun uu____212  ->
                FStar_TypeChecker_Tc.check_module env2 prims_mod) in
         (match uu____198 with
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
        fun uu____265  ->
          match uu____265 with
          | (frag,is_interface_dependence) ->
              (try
                 let uu____307 = FStar_Parser_Driver.parse_fragment frag in
                 match uu____307 with
                 | FStar_Parser_Driver.Empty  ->
                     FStar_Pervasives_Native.Some (curmod, dsenv, env)
                 | FStar_Parser_Driver.Modul ast_modul ->
                     let uu____329 =
                       FStar_ToSyntax_Interleave.interleave_module dsenv
                         ast_modul false in
                     (match uu____329 with
                      | (ds_env,ast_modul1) ->
                          let uu____346 =
                            FStar_ToSyntax_ToSyntax.desugar_partial_modul
                              curmod dsenv ast_modul1 in
                          (match uu____346 with
                           | (dsenv1,modul) ->
                               let dsenv2 =
                                 if is_interface_dependence
                                 then
                                   FStar_ToSyntax_Env.set_iface dsenv1 false
                                 else dsenv1 in
                               let env1 =
                                 match curmod with
                                 | FStar_Pervasives_Native.Some modul1 ->
                                     let uu____367 =
                                       let uu____368 =
                                         let uu____369 =
                                           let uu____370 =
                                             FStar_Options.file_list () in
                                           FStar_List.hd uu____370 in
                                         FStar_Parser_Dep.lowercase_module_name
                                           uu____369 in
                                       let uu____373 =
                                         let uu____374 =
                                           FStar_Ident.string_of_lid
                                             modul1.FStar_Syntax_Syntax.name in
                                         FStar_String.lowercase uu____374 in
                                       uu____368 <> uu____373 in
                                     if uu____367
                                     then
                                       FStar_Exn.raise
                                         (FStar_Errors.Err
                                            "Interactive mode only supports a single module at the top-level")
                                     else env
                                 | FStar_Pervasives_Native.None  -> env in
                               let uu____376 =
                                 let uu____385 =
                                   FStar_ToSyntax_Env.syntax_only dsenv2 in
                                 if uu____385
                                 then (modul, [], env1)
                                 else
                                   FStar_TypeChecker_Tc.tc_partial_modul env1
                                     modul in
                               (match uu____376 with
                                | (modul1,uu____408,env2) ->
                                    FStar_Pervasives_Native.Some
                                      ((FStar_Pervasives_Native.Some modul1),
                                        dsenv2, env2))))
                 | FStar_Parser_Driver.Decls ast_decls ->
                     let uu____427 =
                       FStar_Util.fold_map
                         FStar_ToSyntax_Interleave.prefix_with_interface_decls
                         dsenv ast_decls in
                     (match uu____427 with
                      | (dsenv1,ast_decls_l) ->
                          let uu____458 =
                            FStar_ToSyntax_ToSyntax.desugar_decls dsenv1
                              (FStar_List.flatten ast_decls_l) in
                          (match uu____458 with
                           | (dsenv2,decls) ->
                               (match curmod with
                                | FStar_Pervasives_Native.None  ->
                                    (FStar_Util.print_error
                                       "fragment without an enclosing module";
                                     FStar_All.exit (Prims.parse_int "1"))
                                | FStar_Pervasives_Native.Some modul ->
                                    let uu____497 =
                                      let uu____506 =
                                        FStar_ToSyntax_Env.syntax_only dsenv2 in
                                      if uu____506
                                      then (modul, [], env)
                                      else
                                        FStar_TypeChecker_Tc.tc_more_partial_modul
                                          env modul decls in
                                    (match uu____497 with
                                     | (modul1,uu____529,env1) ->
                                         FStar_Pervasives_Native.Some
                                           ((FStar_Pervasives_Native.Some
                                               modul1), dsenv2, env1)))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____562 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____562 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)];
                    FStar_Pervasives_Native.None)
               | FStar_Errors.Err msg when
                   let uu____581 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____581 ->
                   (FStar_TypeChecker_Err.add_errors env
                      [(msg, FStar_Range.dummyRange)];
                    FStar_Pervasives_Native.None)
               | e when
                   let uu____600 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____600 -> FStar_Exn.raise e)
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
                 (FStar_Util.Inl (FStar_Parser_AST.Interface
                  (l,decls,uu____682)),uu____683)
                 ->
                 let uu____728 =
                   FStar_ToSyntax_Interleave.initialize_interface l decls
                     dsenv in
                 (uu____728, env)
             | FStar_Util.Inl uu____729 ->
                 let uu____754 =
                   let uu____755 =
                     FStar_Util.format1
                       "Unexpected result from parsing %s; expected a single interface"
                       interface_file_name in
                   FStar_Errors.Err uu____755 in
                 FStar_Exn.raise uu____754
             | FStar_Util.Inr (err1,rng) ->
                 FStar_Exn.raise (FStar_Errors.Error (err1, rng))
           with
           | FStar_Errors.Error (msg,r) when
               let uu____791 = FStar_Options.trace_error () in
               Prims.op_Negation uu____791 ->
               (FStar_TypeChecker_Err.add_errors env [(msg, r)]; (dsenv, env))
           | FStar_Errors.Err msg when
               let uu____802 = FStar_Options.trace_error () in
               Prims.op_Negation uu____802 ->
               (FStar_TypeChecker_Err.add_errors env
                  [(msg, FStar_Range.dummyRange)];
                (dsenv, env))
           | e when
               let uu____813 = FStar_Options.trace_error () in
               Prims.op_Negation uu____813 -> FStar_Exn.raise e)
let tc_one_file:
  FStar_ToSyntax_Env.env ->
    FStar_TypeChecker_Env.env ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((FStar_Syntax_Syntax.modul,Prims.int)
             FStar_Pervasives_Native.tuple2,FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
            FStar_Pervasives_Native.tuple3
  =
  fun dsenv  ->
    fun env  ->
      fun pre_fn  ->
        fun fn  ->
          let checked_file_name =
            let uu____859 = FStar_Parser_ParseIt.find_file fn in
            Prims.strcat uu____859 ".checked" in
          let lax_checked_file_name = Prims.strcat checked_file_name ".lax" in
          let lax_ok =
            let uu____862 = FStar_Options.should_verify_file fn in
            Prims.op_Negation uu____862 in
          let cache_file_to_write =
            if lax_ok then lax_checked_file_name else checked_file_name in
          let cache_file_to_read uu____870 =
            if FStar_Util.file_exists checked_file_name
            then FStar_Pervasives_Native.Some checked_file_name
            else
              if lax_ok && (FStar_Util.file_exists lax_checked_file_name)
              then FStar_Pervasives_Native.Some lax_checked_file_name
              else FStar_Pervasives_Native.None in
          let tc_source_file uu____890 =
            let uu____891 = parse dsenv pre_fn fn in
            match uu____891 with
            | (dsenv1,fmod) ->
                let check_mod uu____921 =
                  let uu____922 =
                    FStar_Util.record_time
                      (fun uu____936  ->
                         FStar_TypeChecker_Tc.check_module env fmod) in
                  match uu____922 with
                  | ((tcmod,env1),time) -> ((tcmod, time), dsenv1, env1) in
                let uu____958 =
                  let uu____969 =
                    (FStar_Options.should_verify
                       (fmod.FStar_Syntax_Syntax.name).FStar_Ident.str)
                      &&
                      ((FStar_Options.record_hints ()) ||
                         (FStar_Options.use_hints ())) in
                  if uu____969
                  then
                    let uu____980 = FStar_Parser_ParseIt.find_file fn in
                    FStar_SMTEncoding_Solver.with_hints_db uu____980
                      check_mod
                  else check_mod () in
                (match uu____958 with
                 | (tcmod,dsenv2,tcenv) ->
                     ((let uu____1014 =
                         FStar_Options.cache_checked_modules () in
                       if uu____1014
                       then
                         let uu____1015 = tcmod in
                         match uu____1015 with
                         | (tcmod1,uu____1021) ->
                             let mii =
                               FStar_ToSyntax_Env.inclusion_info dsenv2
                                 tcmod1.FStar_Syntax_Syntax.name in
                             let uu____1023 =
                               let uu____1030 = FStar_Util.digest_of_file fn in
                               (uu____1030, tcmod1, mii) in
                             FStar_Util.save_value_to_file
                               cache_file_to_write uu____1023
                       else ());
                      (tcmod, dsenv2, tcenv))) in
          let uu____1042 = FStar_Options.cache_checked_modules () in
          if uu____1042
          then
            match cache_file_to_read () with
            | FStar_Pervasives_Native.None  -> tc_source_file ()
            | FStar_Pervasives_Native.Some cache_file ->
                let uu____1064 = FStar_Util.load_value_from_file cache_file in
                (match uu____1064 with
                 | FStar_Pervasives_Native.None  ->
                     failwith (Prims.strcat "Corrupt file: " cache_file)
                 | FStar_Pervasives_Native.Some (digest,tcmod,mii) ->
                     let uu____1114 =
                       let uu____1115 = FStar_Util.digest_of_file fn in
                       digest = uu____1115 in
                     if uu____1114
                     then
                       let dsenv1 =
                         FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod mii
                           dsenv in
                       let tcenv =
                         FStar_TypeChecker_Tc.load_checked_module env tcmod in
                       ((tcmod, (Prims.parse_int "0")), dsenv1, tcenv)
                     else
                       (let uu____1133 =
                          FStar_Util.format1
                            "The file %s is stale; delete it" cache_file in
                        failwith uu____1133))
          else tc_source_file ()
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu____1156 = FStar_Util.get_file_extension intf in
          FStar_List.mem uu____1156 ["fsti"; "fsi"]))
        &&
        (let uu____1158 = FStar_Util.get_file_extension impl in
         FStar_List.mem uu____1158 ["fst"; "fs"])
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____1168 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____1168 FStar_Pervasives.ignore);
      (let uu____1170 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____1170 FStar_Pervasives.ignore);
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string ->
      (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1185  ->
    fun msg  ->
      match uu____1185 with
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
      let uu____1233 = uenv in
      match uu____1233 with
      | (dsenv,env) ->
          let uu____1254 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____1296 =
                  tc_one_file dsenv env (FStar_Pervasives_Native.Some intf)
                    impl in
                (match uu____1296 with
                 | (m,dsenv1,env1) -> (remaining1, ([m], dsenv1, env1)))
            | intf_or_impl::remaining1 ->
                let uu____1368 =
                  tc_one_file dsenv env FStar_Pervasives_Native.None
                    intf_or_impl in
                (match uu____1368 with
                 | (m,dsenv1,env1) -> (remaining1, ([m], dsenv1, env1)))
            | [] -> ([], ([], dsenv, env)) in
          (match uu____1254 with
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
      | uu____1574 ->
          let uu____1577 = acc in
          (match uu____1577 with
           | (mods,uenv) ->
               let uu____1612 = tc_one_file_from_remaining remaining uenv in
               (match uu____1612 with
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
        let uu____1707 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____1707 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____1764 =
                (FStar_Options.interactive ()) &&
                  (let uu____1766 = FStar_Errors.get_err_count () in
                   uu____1766 = (Prims.parse_int "0")) in
              if uu____1764
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
    let uu____1794 = tc_prims () in
    match uu____1794 with
    | (prims_mod,dsenv,env) ->
        ((let uu____1829 =
            (let uu____1832 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1832) && (FStar_Options.debug_any ()) in
          if uu____1829
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1835 =
                let uu____1836 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1836 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1835))
          else ());
         (let uu____1840 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____1840 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))