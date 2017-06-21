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
<<<<<<< HEAD
        (let uu___143_111 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___143_111.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___143_111.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___143_111.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___143_111.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___143_111.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___143_111.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___143_111.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___143_111.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___143_111.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___143_111.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___143_111.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___143_111.FStar_TypeChecker_Env.refresh)
=======
        (let uu___222_116 = FStar_SMTEncoding_Solver.solver in
         {
           FStar_TypeChecker_Env.init =
             (uu___222_116.FStar_TypeChecker_Env.init);
           FStar_TypeChecker_Env.push =
             (uu___222_116.FStar_TypeChecker_Env.push);
           FStar_TypeChecker_Env.pop =
             (uu___222_116.FStar_TypeChecker_Env.pop);
           FStar_TypeChecker_Env.mark =
             (uu___222_116.FStar_TypeChecker_Env.mark);
           FStar_TypeChecker_Env.reset_mark =
             (uu___222_116.FStar_TypeChecker_Env.reset_mark);
           FStar_TypeChecker_Env.commit_mark =
             (uu___222_116.FStar_TypeChecker_Env.commit_mark);
           FStar_TypeChecker_Env.encode_modul =
             (uu___222_116.FStar_TypeChecker_Env.encode_modul);
           FStar_TypeChecker_Env.encode_sig =
             (uu___222_116.FStar_TypeChecker_Env.encode_sig);
           FStar_TypeChecker_Env.preprocess =
             FStar_Tactics_Interpreter.preprocess;
           FStar_TypeChecker_Env.solve =
             (uu___222_116.FStar_TypeChecker_Env.solve);
           FStar_TypeChecker_Env.is_trivial =
             (uu___222_116.FStar_TypeChecker_Env.is_trivial);
           FStar_TypeChecker_Env.finish =
             (uu___222_116.FStar_TypeChecker_Env.finish);
           FStar_TypeChecker_Env.refresh =
             (uu___222_116.FStar_TypeChecker_Env.refresh)
>>>>>>> origin/guido_tactics
         }) in
    let env =
      FStar_TypeChecker_Env.initial_env
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Syntax_Const.prims_lid in
    let env1 =
      let uu___223_119 = env in
      {
        FStar_TypeChecker_Env.solver =
          (uu___223_119.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___223_119.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___223_119.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___223_119.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___223_119.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___223_119.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___223_119.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___223_119.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___223_119.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___223_119.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___223_119.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___223_119.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___223_119.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___223_119.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___223_119.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___223_119.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___223_119.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___223_119.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___223_119.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___223_119.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.type_of =
          (uu___223_119.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___223_119.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___223_119.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___223_119.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___223_119.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth = FStar_Tactics_Interpreter.synth;
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___223_119.FStar_TypeChecker_Env.is_native_tactic)
      } in
    let env2 =
      let uu___224_121 = env1 in
      {
        FStar_TypeChecker_Env.solver =
          (uu___224_121.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___224_121.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___224_121.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___224_121.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___224_121.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___224_121.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___224_121.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___224_121.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___224_121.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___224_121.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___224_121.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___224_121.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___224_121.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___224_121.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___224_121.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___224_121.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___224_121.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___224_121.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___224_121.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___224_121.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.type_of =
          (uu___224_121.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___224_121.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___224_121.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___224_121.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___224_121.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___224_121.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          FStar_Tactics_Native.is_native_tactic
      } in
    (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env2;
    (let prims_filename = FStar_Options.prims () in
     let uu____124 =
       let uu____128 = FStar_ToSyntax_Env.empty_env () in
       parse uu____128 None prims_filename in
     match uu____124 with
     | (dsenv,prims_mod) ->
         let uu____138 =
           FStar_Util.record_time
<<<<<<< HEAD
             (fun uu____138  ->
                let uu____139 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env uu____139) in
         (match uu____129 with
          | ((prims_mod1,env1),elapsed_time) ->
              ((prims_mod1, elapsed_time), dsenv, env1)))
=======
             (fun uu____145  ->
                let uu____146 = FStar_List.hd prims_mod in
                FStar_TypeChecker_Tc.check_module env2 uu____146) in
         (match uu____138 with
          | ((prims_mod1,env3),elapsed_time) ->
              ((prims_mod1, elapsed_time), dsenv, env3)))
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        fun uu____171  ->
          match uu____171 with
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
=======
        fun uu____182  ->
          match uu____182 with
          | (frag,is_interface_dependence) ->
              (try
                 let uu____204 = FStar_Parser_Driver.parse_fragment frag in
                 match uu____204 with
                 | FStar_Parser_Driver.Empty  -> Some (curmod, dsenv, env)
                 | FStar_Parser_Driver.Modul ast_modul ->
                     let uu____216 =
                       FStar_ToSyntax_Interleave.interleave_module dsenv
                         ast_modul false in
                     (match uu____216 with
                      | (ds_env,ast_modul1) ->
                          let uu____226 =
                            FStar_ToSyntax_ToSyntax.desugar_partial_modul
                              curmod dsenv ast_modul1 in
                          (match uu____226 with
>>>>>>> origin/guido_tactics
                           | (dsenv1,modul) ->
                               let dsenv2 =
                                 if is_interface_dependence
                                 then
                                   FStar_ToSyntax_Env.set_iface dsenv1 false
                                 else dsenv1 in
                               let env1 =
                                 match curmod with
                                 | Some modul1 ->
<<<<<<< HEAD
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
=======
                                     let uu____240 =
                                       let uu____241 =
                                         let uu____242 =
                                           let uu____243 =
                                             FStar_Options.file_list () in
                                           FStar_List.hd uu____243 in
                                         FStar_Parser_Dep.lowercase_module_name
                                           uu____242 in
                                       let uu____245 =
                                         let uu____246 =
                                           FStar_Ident.string_of_lid
                                             modul1.FStar_Syntax_Syntax.name in
                                         FStar_String.lowercase uu____246 in
                                       uu____241 <> uu____245 in
                                     if uu____240
>>>>>>> origin/guido_tactics
                                     then
                                       raise
                                         (FStar_Errors.Err
                                            "Interactive mode only supports a single module at the top-level")
                                     else env
                                 | None  -> env in
<<<<<<< HEAD
                               let uu____239 =
                                 let uu____244 =
                                   FStar_ToSyntax_Env.syntax_only dsenv2 in
                                 if uu____244
=======
                               let uu____248 =
                                 let uu____253 =
                                   FStar_ToSyntax_Env.syntax_only dsenv2 in
                                 if uu____253
>>>>>>> origin/guido_tactics
                                 then (modul, [], env1)
                                 else
                                   FStar_TypeChecker_Tc.tc_partial_modul env1
                                     modul in
<<<<<<< HEAD
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
=======
                               (match uu____248 with
                                | (modul1,uu____266,env2) ->
                                    Some ((Some modul1), dsenv2, env2))))
                 | FStar_Parser_Driver.Decls ast_decls ->
                     let uu____277 =
                       FStar_Util.fold_map
                         FStar_ToSyntax_Interleave.prefix_with_interface_decls
                         dsenv ast_decls in
                     (match uu____277 with
                      | (dsenv1,ast_decls_l) ->
                          let uu____294 =
                            FStar_ToSyntax_ToSyntax.desugar_decls dsenv1
                              (FStar_List.flatten ast_decls_l) in
                          (match uu____294 with
>>>>>>> origin/guido_tactics
                           | (dsenv2,decls) ->
                               (match curmod with
                                | None  ->
                                    (FStar_Util.print_error
                                       "fragment without an enclosing module";
                                     FStar_All.exit (Prims.parse_int "1"))
                                | Some modul ->
<<<<<<< HEAD
                                    let uu____307 =
                                      let uu____312 =
                                        FStar_ToSyntax_Env.syntax_only dsenv2 in
                                      if uu____312
=======
                                    let uu____316 =
                                      let uu____321 =
                                        FStar_ToSyntax_Env.syntax_only dsenv2 in
                                      if uu____321
>>>>>>> origin/guido_tactics
                                      then (modul, [], env)
                                      else
                                        FStar_TypeChecker_Tc.tc_more_partial_modul
                                          env modul decls in
<<<<<<< HEAD
                                    (match uu____307 with
                                     | (modul1,uu____325,env1) ->
                                         Some ((Some modul1), dsenv2, env1)))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____346 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____346 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
               | FStar_Errors.Err msg when
                   let uu____357 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____357 ->
=======
                                    (match uu____316 with
                                     | (modul1,uu____334,env1) ->
                                         Some ((Some modul1), dsenv2, env1)))))
               with
               | FStar_Errors.Error (msg,r) when
                   let uu____351 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____351 ->
                   (FStar_TypeChecker_Err.add_errors env [(msg, r)]; None)
               | FStar_Errors.Err msg when
                   let uu____362 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____362 ->
>>>>>>> origin/guido_tactics
                   (FStar_TypeChecker_Err.add_errors env
                      [(msg, FStar_Range.dummyRange)];
                    None)
               | e when
<<<<<<< HEAD
                   let uu____368 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____368 -> raise e)
=======
                   let uu____373 = FStar_Options.trace_error () in
                   Prims.op_Negation uu____373 -> raise e)
>>>>>>> origin/guido_tactics
let load_interface_decls:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    FStar_Parser_ParseIt.filename ->
      (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
<<<<<<< HEAD
  fun uu____382  ->
    fun interface_file_name  ->
      match uu____382 with
=======
  fun uu____389  ->
    fun interface_file_name  ->
      match uu____389 with
>>>>>>> origin/guido_tactics
      | (dsenv,env) ->
          (try
             let r =
               FStar_Parser_ParseIt.parse
                 (FStar_Util.Inl interface_file_name) in
             match r with
             | FStar_Util.Inl
                 (FStar_Util.Inl ((FStar_Parser_AST.Interface
                  (l,decls,uu____418))::[]),uu____419)
                 ->
                 let uu____445 =
                   FStar_ToSyntax_Interleave.initialize_interface l decls
                     dsenv in
                 (uu____445, env)
             | FStar_Util.Inl uu____446 ->
                 let uu____459 =
                   let uu____460 =
                     FStar_Util.format1
                       "Unexpected result from parsing %s; expected a single interface"
                       interface_file_name in
                   FStar_Errors.Err uu____460 in
                 raise uu____459
             | FStar_Util.Inr (err1,rng) ->
                 raise (FStar_Errors.Error (err1, rng))
           with
           | FStar_Errors.Error (msg,r) when
<<<<<<< HEAD
               let uu____483 = FStar_Options.trace_error () in
               Prims.op_Negation uu____483 ->
               (FStar_TypeChecker_Err.add_errors env [(msg, r)]; (dsenv, env))
           | FStar_Errors.Err msg when
               let uu____490 = FStar_Options.trace_error () in
               Prims.op_Negation uu____490 ->
=======
               let uu____479 = FStar_Options.trace_error () in
               Prims.op_Negation uu____479 ->
               (FStar_TypeChecker_Err.add_errors env [(msg, r)]; (dsenv, env))
           | FStar_Errors.Err msg when
               let uu____486 = FStar_Options.trace_error () in
               Prims.op_Negation uu____486 ->
>>>>>>> origin/guido_tactics
               (FStar_TypeChecker_Err.add_errors env
                  [(msg, FStar_Range.dummyRange)];
                (dsenv, env))
           | e when
<<<<<<< HEAD
               let uu____497 = FStar_Options.trace_error () in
               Prims.op_Negation uu____497 -> raise e)
=======
               let uu____493 = FStar_Options.trace_error () in
               Prims.op_Negation uu____493 -> raise e)
>>>>>>> origin/guido_tactics
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
          let uu____526 = parse dsenv pre_fn fn in
          match uu____526 with
          | (dsenv1,fmods) ->
              let check_mods uu____549 =
                let uu____550 =
                  FStar_All.pipe_right fmods
                    (FStar_List.fold_left
<<<<<<< HEAD
                       (fun uu____575  ->
                          fun m  ->
                            match uu____575 with
                            | (env1,all_mods) ->
                                let uu____595 =
                                  FStar_Util.record_time
                                    (fun uu____603  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____595 with
=======
                       (fun uu____567  ->
                          fun m  ->
                            match uu____567 with
                            | (env1,all_mods) ->
                                let uu____587 =
                                  FStar_Util.record_time
                                    (fun uu____594  ->
                                       FStar_TypeChecker_Tc.check_module env1
                                         m) in
                                (match uu____587 with
>>>>>>> origin/guido_tactics
                                 | ((m1,env2),elapsed_ms) ->
                                     (env2, ((m1, elapsed_ms) :: all_mods))))
                       (env, [])) in
                match uu____550 with
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
<<<<<<< HEAD
                   let uu____650 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____650
                     check_mods
               | uu____657 -> check_mods ())
=======
                   let uu____641 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu____641
                     check_mods
               | uu____648 -> check_mods ())
>>>>>>> origin/guido_tactics
let needs_interleaving: Prims.string -> Prims.string -> Prims.bool =
  fun intf  ->
    fun impl  ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
<<<<<<< HEAD
         (let uu____668 = FStar_Util.get_file_extension intf in
          uu____668 = "fsti"))
        &&
        (let uu____670 = FStar_Util.get_file_extension impl in
         uu____670 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____678 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____678 FStar_Pervasives.ignore);
      (let uu____680 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____680 FStar_Pervasives.ignore);
=======
         (let uu____660 = FStar_Util.get_file_extension intf in
          uu____660 = "fsti"))
        &&
        (let uu____661 = FStar_Util.get_file_extension impl in
         uu____661 = "fst")
let pop_context: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  ->
      (let uu____671 = FStar_ToSyntax_Env.pop () in
       FStar_All.pipe_right uu____671 FStar_Pervasives.ignore);
      (let uu____673 = FStar_TypeChecker_Env.pop env msg in
       FStar_All.pipe_right uu____673 FStar_Pervasives.ignore);
>>>>>>> origin/guido_tactics
      (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ()
let push_context:
  (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env) ->
    Prims.string -> (FStar_ToSyntax_Env.env* FStar_TypeChecker_Env.env)
  =
<<<<<<< HEAD
  fun uu____689  ->
    fun msg  ->
      match uu____689 with
=======
  fun uu____684  ->
    fun msg  ->
      match uu____684 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      let uu____718 = uenv in
      match uu____718 with
      | (dsenv,env) ->
          let uu____730 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____753 = tc_one_file dsenv env (Some intf) impl in
                (remaining1, uu____753)
            | intf_or_impl::remaining1 ->
                let uu____770 = tc_one_file dsenv env None intf_or_impl in
                (remaining1, uu____770)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____730 with
=======
      let uu____715 = uenv in
      match uu____715 with
      | (dsenv,env) ->
          let uu____727 =
            match remaining with
            | intf::impl::remaining1 when needs_interleaving intf impl ->
                let uu____750 = tc_one_file dsenv env (Some intf) impl in
                (remaining1, uu____750)
            | intf_or_impl::remaining1 ->
                let uu____767 = tc_one_file dsenv env None intf_or_impl in
                (remaining1, uu____767)
            | [] -> ([], ([], dsenv, env)) in
          (match uu____727 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
      | uu____857 ->
          let uu____859 = acc in
          (match uu____859 with
           | (mods,uenv) ->
               let uu____878 = tc_one_file_from_remaining remaining uenv in
               (match uu____878 with
=======
      | uu____856 ->
          let uu____858 = acc in
          (match uu____858 with
           | (mods,uenv) ->
               let uu____877 = tc_one_file_from_remaining remaining uenv in
               (match uu____877 with
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
        let uu____931 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____931 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____962 =
                (FStar_Options.interactive ()) &&
                  (let uu____964 = FStar_Errors.get_err_count () in
                   uu____964 = (Prims.parse_int "0")) in
              if uu____962
=======
        let uu____933 = tc_fold_interleave ([], (dsenv, env)) filenames in
        match uu____933 with
        | (all_mods,(dsenv1,env1)) ->
            ((let uu____964 =
                (FStar_Options.interactive ()) &&
                  (let uu____965 = FStar_Errors.get_err_count () in
                   uu____965 = (Prims.parse_int "0")) in
              if uu____964
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    let uu____980 = tc_prims () in
    match uu____980 with
    | (prims_mod,dsenv,env) ->
        ((let uu____1000 =
            (let uu____1003 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1003) && (FStar_Options.debug_any ()) in
          if uu____1000
=======
    let uu____982 = tc_prims () in
    match uu____982 with
    | (prims_mod,dsenv,env) ->
        ((let uu____1002 =
            (let uu____1003 = FStar_Options.explicit_deps () in
             Prims.op_Negation uu____1003) && (FStar_Options.debug_any ()) in
          if uu____1002
>>>>>>> origin/guido_tactics
          then
            (FStar_Util.print_endline
               "Auto-deps kicked in; here's some info.";
             FStar_Util.print1
               "Here's the list of filenames we will process: %s\n"
               (FStar_String.concat " " filenames);
             (let uu____1006 =
                let uu____1007 = FStar_Options.verify_module () in
                FStar_String.concat " " uu____1007 in
              FStar_Util.print1
                "Here's the list of modules we will verify: %s\n" uu____1006))
          else ());
         (let uu____1010 = batch_mode_tc_no_prims dsenv env filenames in
          match uu____1010 with
          | (all_mods,dsenv1,env1) -> ((prims_mod :: all_mods), dsenv1, env1)))