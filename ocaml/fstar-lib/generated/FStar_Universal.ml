open Prims
type uenv = FStar_Extraction_ML_UEnv.uenv
let (module_or_interface_name :
  FStar_Syntax_Syntax.modul -> (Prims.bool * FStar_Ident.lid)) =
  fun m ->
    ((m.FStar_Syntax_Syntax.is_interface), (m.FStar_Syntax_Syntax.name))
let with_dsenv_of_tcenv :
  'a .
    FStar_TypeChecker_Env.env ->
      'a FStar_Syntax_DsEnv.withenv -> ('a * FStar_TypeChecker_Env.env)
  =
  fun tcenv ->
    fun f ->
      let uu___ = f tcenv.FStar_TypeChecker_Env.dsenv in
      match uu___ with
      | (a1, dsenv) ->
          (a1,
            {
              FStar_TypeChecker_Env.solver =
                (tcenv.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (tcenv.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (tcenv.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (tcenv.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (tcenv.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (tcenv.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (tcenv.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (tcenv.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (tcenv.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (tcenv.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (tcenv.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (tcenv.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (tcenv.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (tcenv.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (tcenv.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (tcenv.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq_strict =
                (tcenv.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (tcenv.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (tcenv.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (tcenv.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (tcenv.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (tcenv.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (tcenv.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (tcenv.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (tcenv.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (tcenv.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                (tcenv.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStar_TypeChecker_Env.universe_of =
                (tcenv.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (tcenv.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStar_TypeChecker_Env.teq_nosmt_force =
                (tcenv.FStar_TypeChecker_Env.teq_nosmt_force);
              FStar_TypeChecker_Env.subtype_nosmt_force =
                (tcenv.FStar_TypeChecker_Env.subtype_nosmt_force);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (tcenv.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (tcenv.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (tcenv.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (tcenv.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (tcenv.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (tcenv.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (tcenv.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (tcenv.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (tcenv.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (tcenv.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (tcenv.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv = dsenv;
              FStar_TypeChecker_Env.nbe = (tcenv.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (tcenv.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (tcenv.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (tcenv.FStar_TypeChecker_Env.enable_defer_to_tac);
              FStar_TypeChecker_Env.unif_allow_ref_guards =
                (tcenv.FStar_TypeChecker_Env.unif_allow_ref_guards);
              FStar_TypeChecker_Env.erase_erasable_args =
                (tcenv.FStar_TypeChecker_Env.erase_erasable_args);
              FStar_TypeChecker_Env.core_check =
                (tcenv.FStar_TypeChecker_Env.core_check)
            })
let with_tcenv_of_env :
  'a .
    uenv ->
      (FStar_TypeChecker_Env.env -> ('a * FStar_TypeChecker_Env.env)) ->
        ('a * uenv)
  =
  fun e ->
    fun f ->
      let uu___ =
        let uu___1 = FStar_Extraction_ML_UEnv.tcenv_of_uenv e in f uu___1 in
      match uu___ with
      | (a1, t') ->
          let uu___1 = FStar_Extraction_ML_UEnv.set_tcenv e t' in
          (a1, uu___1)
let with_dsenv_of_env :
  'a . uenv -> 'a FStar_Syntax_DsEnv.withenv -> ('a * uenv) =
  fun e ->
    fun f ->
      let uu___ =
        let uu___1 = FStar_Extraction_ML_UEnv.tcenv_of_uenv e in
        with_dsenv_of_tcenv uu___1 f in
      match uu___ with
      | (a1, tcenv) ->
          let uu___1 = FStar_Extraction_ML_UEnv.set_tcenv e tcenv in
          (a1, uu___1)
let (push_env : uenv -> uenv) =
  fun env ->
    let uu___ =
      with_tcenv_of_env env
        (fun tcenv ->
           let uu___1 =
             let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
             FStar_TypeChecker_Env.push uu___2 "top-level: push_env" in
           ((), uu___1)) in
    FStar_Pervasives_Native.snd uu___
let (pop_env : uenv -> uenv) =
  fun env ->
    let uu___ =
      with_tcenv_of_env env
        (fun tcenv ->
           let uu___1 = FStar_TypeChecker_Env.pop tcenv "top-level: pop_env" in
           ((), uu___1)) in
    FStar_Pervasives_Native.snd uu___
let with_env : 'a . uenv -> (uenv -> 'a) -> 'a =
  fun env ->
    fun f ->
      let env1 = push_env env in
      let res = f env1 in let uu___ = pop_env env1 in res
let (env_of_tcenv :
  FStar_TypeChecker_Env.env -> FStar_Extraction_ML_UEnv.uenv) =
  fun env -> FStar_Extraction_ML_UEnv.new_uenv env
let (parse :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> (FStar_Syntax_Syntax.modul * uenv))
  =
  fun env ->
    fun pre_fn ->
      fun fn ->
        let uu___ = FStar_Parser_Driver.parse_file fn in
        match uu___ with
        | (ast, uu___1) ->
            let uu___2 =
              match pre_fn with
              | FStar_Pervasives_Native.None -> (ast, env)
              | FStar_Pervasives_Native.Some pre_fn1 ->
                  let uu___3 = FStar_Parser_Driver.parse_file pre_fn1 in
                  (match uu___3 with
                   | (pre_ast, uu___4) ->
                       (match (pre_ast, ast) with
                        | (FStar_Parser_AST.Interface (lid1, decls1, uu___5),
                           FStar_Parser_AST.Module (lid2, decls2)) when
                            FStar_Ident.lid_equals lid1 lid2 ->
                            let uu___6 =
                              let uu___7 =
                                FStar_ToSyntax_Interleave.initialize_interface
                                  lid1 decls1 in
                              with_dsenv_of_env env uu___7 in
                            (match uu___6 with
                             | (uu___7, env1) ->
                                 let uu___8 =
                                   FStar_ToSyntax_Interleave.interleave_module
                                     ast true in
                                 with_dsenv_of_env env1 uu___8)
                        | uu___5 ->
                            FStar_Errors.raise_err
                              (FStar_Errors.Fatal_PreModuleMismatch,
                                "mismatch between pre-module and module\n"))) in
            (match uu___2 with
             | (ast1, env1) ->
                 let uu___3 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul ast1 in
                 with_dsenv_of_env env1 uu___3)
let (core_check : FStar_TypeChecker_Env.core_check_t) =
  fun env ->
    fun tm ->
      fun t ->
        fun must_tot ->
          let uu___ =
            let uu___1 = FStar_Options.compat_pre_core_should_check () in
            Prims.op_Negation uu___1 in
          if uu___
          then FStar_Pervasives.Inl FStar_Pervasives_Native.None
          else
            (let uu___2 = FStar_TypeChecker_Core.check_term env tm t must_tot in
             match uu___2 with
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
                 FStar_Pervasives.Inl FStar_Pervasives_Native.None
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
                 let uu___3 = FStar_Options.compat_pre_core_set () in
                 if uu___3
                 then FStar_Pervasives.Inl FStar_Pervasives_Native.None
                 else FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
             | FStar_Pervasives.Inr err ->
                 FStar_Pervasives.Inr
                   ((fun b ->
                       if b
                       then FStar_TypeChecker_Core.print_error_short err
                       else FStar_TypeChecker_Core.print_error err)))
let (init_env : FStar_Parser_Dep.deps -> FStar_TypeChecker_Env.env) =
  fun deps ->
    let solver =
      let uu___ = FStar_Options.lax () in
      if uu___
      then FStar_SMTEncoding_Solver.dummy
      else
        {
          FStar_TypeChecker_Env.init =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.init);
          FStar_TypeChecker_Env.push =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.push);
          FStar_TypeChecker_Env.pop =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.pop);
          FStar_TypeChecker_Env.snapshot =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.snapshot);
          FStar_TypeChecker_Env.rollback =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.rollback);
          FStar_TypeChecker_Env.encode_sig =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.encode_sig);
          FStar_TypeChecker_Env.preprocess = FStar_Tactics_Hooks.preprocess;
          FStar_TypeChecker_Env.spinoff_strictly_positive_goals =
            (FStar_Pervasives_Native.Some
               FStar_Tactics_Hooks.spinoff_strictly_positive_goals);
          FStar_TypeChecker_Env.handle_smt_goal =
            FStar_Tactics_Hooks.handle_smt_goal;
          FStar_TypeChecker_Env.solve =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.solve);
          FStar_TypeChecker_Env.finish =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.finish);
          FStar_TypeChecker_Env.refresh =
            (FStar_SMTEncoding_Solver.solver.FStar_TypeChecker_Env.refresh)
        } in
    let env =
      let uu___ =
        let uu___1 = FStar_Tactics_Interpreter.primitive_steps () in
        FStar_TypeChecker_NBE.normalize uu___1 in
      FStar_TypeChecker_Env.initial_env deps FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term
        FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term_fastpath
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_Rel.teq_nosmt_force
        FStar_TypeChecker_Rel.subtype_nosmt_force solver
        FStar_Parser_Const.prims_lid uu___ core_check in
    let env1 =
      {
        FStar_TypeChecker_Env.solver = (env.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (env.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (env.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (env.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (env.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (env.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (env.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (env.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (env.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (env.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (env.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (env.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (env.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (env.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq_strict =
          (env.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface = (env.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (env.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (env.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard = (env.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (env.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (env.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (env.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
          (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStar_TypeChecker_Env.universe_of =
          (env.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStar_TypeChecker_Env.teq_nosmt_force =
          (env.FStar_TypeChecker_Env.teq_nosmt_force);
        FStar_TypeChecker_Env.subtype_nosmt_force =
          (env.FStar_TypeChecker_Env.subtype_nosmt_force);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (env.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (env.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (env.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns = (env.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook = FStar_Tactics_Hooks.synthesize;
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice = (env.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (env.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (env.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (env.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks = (env.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (env.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (env.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (env.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (env.FStar_TypeChecker_Env.enable_defer_to_tac);
        FStar_TypeChecker_Env.unif_allow_ref_guards =
          (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
        FStar_TypeChecker_Env.erase_erasable_args =
          (env.FStar_TypeChecker_Env.erase_erasable_args);
        FStar_TypeChecker_Env.core_check =
          (env.FStar_TypeChecker_Env.core_check)
      } in
    let env2 =
      {
        FStar_TypeChecker_Env.solver = (env1.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (env1.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (env1.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (env1.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (env1.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (env1.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (env1.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (env1.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (env1.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (env1.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (env1.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (env1.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (env1.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (env1.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (env1.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (env1.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq_strict =
          (env1.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (env1.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (env1.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (env1.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (env1.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (env1.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (env1.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (env1.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (env1.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (env1.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
          (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStar_TypeChecker_Env.universe_of =
          (env1.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStar_TypeChecker_Env.teq_nosmt_force =
          (env1.FStar_TypeChecker_Env.teq_nosmt_force);
        FStar_TypeChecker_Env.subtype_nosmt_force =
          (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (env1.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (env1.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (env1.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (env1.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          FStar_Tactics_Hooks.solve_implicits;
        FStar_TypeChecker_Env.splice = (env1.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (env1.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (env1.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (env1.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (env1.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (env1.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (env1.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (env1.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (env1.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
        FStar_TypeChecker_Env.unif_allow_ref_guards =
          (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
        FStar_TypeChecker_Env.erase_erasable_args =
          (env1.FStar_TypeChecker_Env.erase_erasable_args);
        FStar_TypeChecker_Env.core_check =
          (env1.FStar_TypeChecker_Env.core_check)
      } in
    let env3 =
      {
        FStar_TypeChecker_Env.solver = (env2.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (env2.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (env2.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (env2.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (env2.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (env2.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (env2.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (env2.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (env2.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (env2.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (env2.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (env2.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (env2.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (env2.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (env2.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (env2.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq_strict =
          (env2.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (env2.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (env2.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (env2.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (env2.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (env2.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (env2.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (env2.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (env2.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (env2.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
          (env2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStar_TypeChecker_Env.universe_of =
          (env2.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (env2.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStar_TypeChecker_Env.teq_nosmt_force =
          (env2.FStar_TypeChecker_Env.teq_nosmt_force);
        FStar_TypeChecker_Env.subtype_nosmt_force =
          (env2.FStar_TypeChecker_Env.subtype_nosmt_force);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (env2.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (env2.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (env2.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (env2.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (env2.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (env2.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice = FStar_Tactics_Hooks.splice;
        FStar_TypeChecker_Env.mpreprocess =
          (env2.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (env2.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (env2.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (env2.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (env2.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (env2.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (env2.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (env2.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (env2.FStar_TypeChecker_Env.enable_defer_to_tac);
        FStar_TypeChecker_Env.unif_allow_ref_guards =
          (env2.FStar_TypeChecker_Env.unif_allow_ref_guards);
        FStar_TypeChecker_Env.erase_erasable_args =
          (env2.FStar_TypeChecker_Env.erase_erasable_args);
        FStar_TypeChecker_Env.core_check =
          (env2.FStar_TypeChecker_Env.core_check)
      } in
    let env4 =
      {
        FStar_TypeChecker_Env.solver = (env3.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (env3.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (env3.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (env3.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (env3.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (env3.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (env3.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (env3.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (env3.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (env3.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (env3.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (env3.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (env3.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (env3.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (env3.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (env3.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq_strict =
          (env3.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (env3.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (env3.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (env3.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (env3.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (env3.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (env3.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (env3.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (env3.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (env3.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
          (env3.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStar_TypeChecker_Env.universe_of =
          (env3.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (env3.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStar_TypeChecker_Env.teq_nosmt_force =
          (env3.FStar_TypeChecker_Env.teq_nosmt_force);
        FStar_TypeChecker_Env.subtype_nosmt_force =
          (env3.FStar_TypeChecker_Env.subtype_nosmt_force);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (env3.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (env3.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (env3.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (env3.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (env3.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (env3.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice = (env3.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess = FStar_Tactics_Hooks.mpreprocess;
        FStar_TypeChecker_Env.postprocess =
          (env3.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (env3.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (env3.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (env3.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (env3.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (env3.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (env3.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (env3.FStar_TypeChecker_Env.enable_defer_to_tac);
        FStar_TypeChecker_Env.unif_allow_ref_guards =
          (env3.FStar_TypeChecker_Env.unif_allow_ref_guards);
        FStar_TypeChecker_Env.erase_erasable_args =
          (env3.FStar_TypeChecker_Env.erase_erasable_args);
        FStar_TypeChecker_Env.core_check =
          (env3.FStar_TypeChecker_Env.core_check)
      } in
    let env5 =
      {
        FStar_TypeChecker_Env.solver = (env4.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (env4.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (env4.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (env4.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (env4.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (env4.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (env4.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (env4.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (env4.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (env4.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (env4.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (env4.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (env4.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (env4.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (env4.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (env4.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq_strict =
          (env4.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (env4.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (env4.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (env4.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (env4.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (env4.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (env4.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (env4.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (env4.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (env4.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
          (env4.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStar_TypeChecker_Env.universe_of =
          (env4.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (env4.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStar_TypeChecker_Env.teq_nosmt_force =
          (env4.FStar_TypeChecker_Env.teq_nosmt_force);
        FStar_TypeChecker_Env.subtype_nosmt_force =
          (env4.FStar_TypeChecker_Env.subtype_nosmt_force);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (env4.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (env4.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (env4.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (env4.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (env4.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (env4.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice = (env4.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (env4.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess = FStar_Tactics_Hooks.postprocess;
        FStar_TypeChecker_Env.identifier_info =
          (env4.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (env4.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (env4.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (env4.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (env4.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (env4.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (env4.FStar_TypeChecker_Env.enable_defer_to_tac);
        FStar_TypeChecker_Env.unif_allow_ref_guards =
          (env4.FStar_TypeChecker_Env.unif_allow_ref_guards);
        FStar_TypeChecker_Env.erase_erasable_args =
          (env4.FStar_TypeChecker_Env.erase_erasable_args);
        FStar_TypeChecker_Env.core_check =
          (env4.FStar_TypeChecker_Env.core_check)
      } in
    (env5.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env5; env5
let (tc_one_fragment :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env_t ->
      FStar_Parser_ParseIt.input_frag ->
        (FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option *
          FStar_TypeChecker_Env.env))
  =
  fun curmod ->
    fun env ->
      fun frag ->
        let fname env1 =
          let uu___ = FStar_Options.lsp_server () in
          if uu___
          then
            let uu___1 = FStar_TypeChecker_Env.get_range env1 in
            FStar_Compiler_Range.file_of_range uu___1
          else
            (let uu___2 = FStar_Options.file_list () in
             FStar_Compiler_List.hd uu___2) in
        let acceptable_mod_name modul =
          let uu___ =
            let uu___1 = fname env in
            FStar_Parser_Dep.lowercase_module_name uu___1 in
          let uu___1 =
            let uu___2 =
              FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
            FStar_String.lowercase uu___2 in
          uu___ = uu___1 in
        let range_of_first_mod_decl modul =
          match modul with
          | FStar_Parser_AST.Module
              (uu___,
               { FStar_Parser_AST.d = uu___1; FStar_Parser_AST.drange = d;
                 FStar_Parser_AST.quals = uu___2;
                 FStar_Parser_AST.attrs = uu___3;_}::uu___4)
              -> d
          | FStar_Parser_AST.Interface
              (uu___,
               { FStar_Parser_AST.d = uu___1; FStar_Parser_AST.drange = d;
                 FStar_Parser_AST.quals = uu___2;
                 FStar_Parser_AST.attrs = uu___3;_}::uu___4,
               uu___5)
              -> d
          | uu___ -> FStar_Compiler_Range.dummyRange in
        let uu___ = FStar_Parser_Driver.parse_fragment frag in
        match uu___ with
        | FStar_Parser_Driver.Empty -> (curmod, env)
        | FStar_Parser_Driver.Decls [] -> (curmod, env)
        | FStar_Parser_Driver.Modul ast_modul ->
            let uu___1 =
              let uu___2 =
                FStar_ToSyntax_Interleave.interleave_module ast_modul false in
              FStar_Compiler_Effect.op_Less_Bar (with_dsenv_of_tcenv env)
                uu___2 in
            (match uu___1 with
             | (ast_modul1, env1) ->
                 let uu___2 =
                   let uu___3 =
                     FStar_ToSyntax_ToSyntax.partial_ast_modul_to_modul
                       curmod ast_modul1 in
                   FStar_Compiler_Effect.op_Less_Bar
                     (with_dsenv_of_tcenv env1) uu___3 in
                 (match uu___2 with
                  | (modul, env2) ->
                      ((let uu___4 =
                          let uu___5 = acceptable_mod_name modul in
                          Prims.op_Negation uu___5 in
                        if uu___4
                        then
                          let msg =
                            let uu___5 =
                              let uu___6 = fname env2 in
                              FStar_Parser_Dep.module_name_of_file uu___6 in
                            FStar_Compiler_Util.format1
                              "Interactive mode only supports a single module at the top-level. Expected module %s"
                              uu___5 in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_NonSingletonTopLevelModule,
                              msg) (range_of_first_mod_decl ast_modul1)
                        else ());
                       (let uu___4 =
                          let uu___5 =
                            FStar_Syntax_DsEnv.syntax_only
                              env2.FStar_TypeChecker_Env.dsenv in
                          if uu___5
                          then (modul, env2)
                          else
                            FStar_TypeChecker_Tc.tc_partial_modul env2 modul in
                        match uu___4 with
                        | (modul1, env3) ->
                            ((FStar_Pervasives_Native.Some modul1), env3)))))
        | FStar_Parser_Driver.Decls ast_decls ->
            (match curmod with
             | FStar_Pervasives_Native.None ->
                 let uu___1 = FStar_Compiler_List.hd ast_decls in
                 (match uu___1 with
                  | { FStar_Parser_AST.d = uu___2;
                      FStar_Parser_AST.drange = rng;
                      FStar_Parser_AST.quals = uu___3;
                      FStar_Parser_AST.attrs = uu___4;_} ->
                      FStar_Errors.raise_error
                        (FStar_Errors.Fatal_ModuleFirstStatement,
                          "First statement must be a module declaration") rng)
             | FStar_Pervasives_Native.Some modul ->
                 let uu___1 =
                   FStar_Compiler_Util.fold_map
                     (fun env1 ->
                        fun a_decl ->
                          let uu___2 =
                            let uu___3 =
                              FStar_ToSyntax_Interleave.prefix_with_interface_decls
                                modul.FStar_Syntax_Syntax.name a_decl in
                            FStar_Compiler_Effect.op_Less_Bar
                              (with_dsenv_of_tcenv env1) uu___3 in
                          match uu___2 with | (decls, env2) -> (env2, decls))
                     env ast_decls in
                 (match uu___1 with
                  | (env1, ast_decls_l) ->
                      let uu___2 =
                        let uu___3 =
                          FStar_ToSyntax_ToSyntax.decls_to_sigelts
                            (FStar_Compiler_List.flatten ast_decls_l) in
                        FStar_Compiler_Effect.op_Less_Bar
                          (with_dsenv_of_tcenv env1) uu___3 in
                      (match uu___2 with
                       | (sigelts, env2) ->
                           let uu___3 =
                             let uu___4 =
                               FStar_Syntax_DsEnv.syntax_only
                                 env2.FStar_TypeChecker_Env.dsenv in
                             if uu___4
                             then (modul, [], env2)
                             else
                               FStar_TypeChecker_Tc.tc_more_partial_modul
                                 env2 modul sigelts in
                           (match uu___3 with
                            | (modul1, uu___4, env3) ->
                                ((FStar_Pervasives_Native.Some modul1), env3)))))
let (load_interface_decls :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env_t) =
  fun env ->
    fun interface_file_name ->
      let r =
        FStar_Parser_ParseIt.parse
          (FStar_Parser_ParseIt.Filename interface_file_name) in
      match r with
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Pervasives.Inl (FStar_Parser_AST.Interface
           (l, decls, uu___)), uu___1)
          ->
          let uu___2 =
            let uu___3 =
              FStar_ToSyntax_Interleave.initialize_interface l decls in
            FStar_Compiler_Effect.op_Less_Bar (with_dsenv_of_tcenv env)
              uu___3 in
          FStar_Pervasives_Native.snd uu___2
      | FStar_Parser_ParseIt.ASTFragment uu___ ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_Util.format1
                "Unexpected result from parsing %s; expected a single interface"
                interface_file_name in
            (FStar_Errors.Fatal_ParseErrors, uu___2) in
          FStar_Errors.raise_err uu___1
      | FStar_Parser_ParseIt.ParseError (err, msg, rng) ->
          FStar_Compiler_Effect.raise
            (FStar_Errors.Error (err, msg, rng, []))
      | FStar_Parser_ParseIt.Term uu___ ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
let (emit : FStar_Extraction_ML_Syntax.mllib Prims.list -> unit) =
  fun mllibs ->
    let opt = FStar_Options.codegen () in
    if opt <> FStar_Pervasives_Native.None
    then
      let ext =
        match opt with
        | FStar_Pervasives_Native.Some (FStar_Options.FSharp) -> ".fs"
        | FStar_Pervasives_Native.Some (FStar_Options.OCaml) -> ".ml"
        | FStar_Pervasives_Native.Some (FStar_Options.Plugin) -> ".ml"
        | FStar_Pervasives_Native.Some (FStar_Options.Krml) -> ".krml"
        | uu___ -> failwith "Unrecognized option" in
      match opt with
      | FStar_Pervasives_Native.Some (FStar_Options.FSharp) ->
          let outdir = FStar_Options.output_dir () in
          FStar_Compiler_List.iter
            (FStar_Extraction_ML_PrintML.print outdir ext) mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.OCaml) ->
          let outdir = FStar_Options.output_dir () in
          FStar_Compiler_List.iter
            (FStar_Extraction_ML_PrintML.print outdir ext) mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.Plugin) ->
          let outdir = FStar_Options.output_dir () in
          FStar_Compiler_List.iter
            (FStar_Extraction_ML_PrintML.print outdir ext) mllibs
      | FStar_Pervasives_Native.Some (FStar_Options.Krml) ->
          let programs =
            FStar_Compiler_List.collect FStar_Extraction_Krml.translate
              mllibs in
          let bin = (FStar_Extraction_Krml.current_version, programs) in
          (match programs with
           | (name, uu___)::[] ->
               let uu___1 =
                 FStar_Options.prepend_output_dir (Prims.op_Hat name ext) in
               FStar_Compiler_Util.save_value_to_file uu___1 bin
           | uu___ ->
               let uu___1 = FStar_Options.prepend_output_dir "out.krml" in
               FStar_Compiler_Util.save_value_to_file uu___1 bin)
      | uu___ -> failwith "Unrecognized option"
    else ()
let (tc_one_file :
  uenv ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        FStar_Parser_Dep.parsing_data ->
          (FStar_CheckedFiles.tc_result * FStar_Extraction_ML_Syntax.mllib
            FStar_Pervasives_Native.option * uenv))
  =
  fun env ->
    fun pre_fn ->
      fun fn ->
        fun parsing_data ->
          FStar_Ident.reset_gensym ();
          (let maybe_restore_opts uu___1 =
             let uu___2 =
               let uu___3 = FStar_Options.interactive () in
               Prims.op_Negation uu___3 in
             if uu___2
             then
               let uu___3 = FStar_Options.restore_cmd_line_options true in
               FStar_Compiler_Effect.op_Bar_Greater uu___3 (fun uu___4 -> ())
             else () in
           let maybe_extract_mldefs tcmod env1 =
             let uu___1 = FStar_Options.codegen () in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 (FStar_Pervasives_Native.None, Prims.int_zero)
             | FStar_Pervasives_Native.Some tgt ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       FStar_Ident.string_of_lid
                         tcmod.FStar_Syntax_Syntax.name in
                     FStar_Options.should_extract uu___4 tgt in
                   Prims.op_Negation uu___3 in
                 if uu___2
                 then (FStar_Pervasives_Native.None, Prims.int_zero)
                 else
                   FStar_Compiler_Util.record_time
                     (fun uu___4 ->
                        with_env env1
                          (fun env2 ->
                             let uu___5 =
                               FStar_Extraction_ML_Modul.extract env2 tcmod in
                             match uu___5 with | (uu___6, defs) -> defs)) in
           let maybe_extract_ml_iface tcmod env1 =
             let uu___1 =
               let uu___2 = FStar_Options.codegen () in
               uu___2 = FStar_Pervasives_Native.None in
             if uu___1
             then (env1, Prims.int_zero)
             else
               FStar_Compiler_Util.record_time
                 (fun uu___3 ->
                    let uu___4 =
                      with_env env1
                        (fun env2 ->
                           FStar_Extraction_ML_Modul.extract_iface env2 tcmod) in
                    match uu___4 with | (env2, uu___5) -> env2) in
           let tc_source_file uu___1 =
             let uu___2 = parse env pre_fn fn in
             match uu___2 with
             | (fmod, env1) ->
                 let mii =
                   let uu___3 =
                     let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env1 in
                     uu___4.FStar_TypeChecker_Env.dsenv in
                   FStar_Syntax_DsEnv.inclusion_info uu___3
                     fmod.FStar_Syntax_Syntax.name in
                 let check_mod uu___3 =
                   let check env2 =
                     (let uu___5 =
                        let uu___6 = FStar_Options.lax () in
                        Prims.op_Negation uu___6 in
                      if uu___5 then FStar_SMTEncoding_Z3.refresh () else ());
                     with_tcenv_of_env env2
                       (fun tcenv ->
                          (match tcenv.FStar_TypeChecker_Env.gamma with
                           | [] -> ()
                           | uu___6 ->
                               failwith
                                 "Impossible: gamma contains leaked names");
                          (let uu___6 =
                             FStar_TypeChecker_Tc.check_module tcenv fmod
                               (FStar_Compiler_Util.is_some pre_fn) in
                           match uu___6 with
                           | (modul, env3) ->
                               (maybe_restore_opts ();
                                (let smt_decls =
                                   let uu___8 =
                                     let uu___9 = FStar_Options.lax () in
                                     Prims.op_Negation uu___9 in
                                   if uu___8
                                   then
                                     FStar_SMTEncoding_Encode.encode_modul
                                       env3 modul
                                   else ([], []) in
                                 ((modul, smt_decls), env3))))) in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_Ident.string_of_lid
                           fmod.FStar_Syntax_Syntax.name in
                       FStar_Pervasives_Native.Some uu___6 in
                     FStar_Profiling.profile (fun uu___6 -> check env1)
                       uu___5 "FStar.Universal.tc_source_file" in
                   match uu___4 with
                   | ((tcmod, smt_decls), env2) ->
                       let tc_time = Prims.int_zero in
                       let uu___5 = maybe_extract_mldefs tcmod env2 in
                       (match uu___5 with
                        | (extracted_defs, extract_time) ->
                            let uu___6 = maybe_extract_ml_iface tcmod env2 in
                            (match uu___6 with
                             | (env3, iface_extraction_time) ->
                                 ({
                                    FStar_CheckedFiles.checked_module = tcmod;
                                    FStar_CheckedFiles.mii = mii;
                                    FStar_CheckedFiles.smt_decls = smt_decls;
                                    FStar_CheckedFiles.tc_time = tc_time;
                                    FStar_CheckedFiles.extraction_time =
                                      (extract_time + iface_extraction_time)
                                  }, extracted_defs, env3))) in
                 let uu___3 =
                   (let uu___4 =
                      FStar_Ident.string_of_lid fmod.FStar_Syntax_Syntax.name in
                    FStar_Options.should_verify uu___4) &&
                     ((FStar_Options.record_hints ()) ||
                        (FStar_Options.use_hints ())) in
                 if uu___3
                 then
                   let uu___4 = FStar_Parser_ParseIt.find_file fn in
                   FStar_SMTEncoding_Solver.with_hints_db uu___4 check_mod
                 else check_mod () in
           let uu___1 =
             let uu___2 = FStar_Options.cache_off () in
             Prims.op_Negation uu___2 in
           if uu___1
           then
             let r = FStar_CheckedFiles.load_module_from_cache env fn in
             let r1 =
               let uu___2 =
                 (FStar_Options.force ()) &&
                   (FStar_Options.should_check_file fn) in
               if uu___2 then FStar_Pervasives_Native.None else r in
             match r1 with
             | FStar_Pervasives_Native.None ->
                 ((let uu___3 =
                     let uu___4 = FStar_Parser_Dep.module_name_of_file fn in
                     FStar_Options.should_be_already_cached uu___4 in
                   if uu___3
                   then
                     let uu___4 =
                       let uu___5 =
                         FStar_Compiler_Util.format1
                           "Expected %s to already be checked" fn in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu___5) in
                     FStar_Errors.raise_err uu___4
                   else ());
                  (let uu___4 =
                     (let uu___5 = FStar_Options.codegen () in
                      FStar_Compiler_Option.isSome uu___5) &&
                       (FStar_Options.cmi ()) in
                   if uu___4
                   then
                     let uu___5 =
                       let uu___6 =
                         FStar_Compiler_Util.format1
                           "Cross-module inlining expects all modules to be checked first; %s was not checked"
                           fn in
                       (FStar_Errors.Error_AlreadyCachedAssertionFailure,
                         uu___6) in
                     FStar_Errors.raise_err uu___5
                   else ());
                  (let uu___4 = tc_source_file () in
                   match uu___4 with
                   | (tc_result, mllib, env1) ->
                       ((let uu___6 =
                           (let uu___7 = FStar_Errors.get_err_count () in
                            uu___7 = Prims.int_zero) &&
                             ((FStar_Options.lax ()) ||
                                (let uu___7 =
                                   FStar_Ident.string_of_lid
                                     (tc_result.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name in
                                 FStar_Options.should_verify uu___7)) in
                         if uu___6
                         then
                           FStar_CheckedFiles.store_module_to_cache env1 fn
                             parsing_data tc_result
                         else ());
                        (tc_result, mllib, env1))))
             | FStar_Pervasives_Native.Some tc_result ->
                 let tcmod = tc_result.FStar_CheckedFiles.checked_module in
                 let smt_decls = tc_result.FStar_CheckedFiles.smt_decls in
                 ((let uu___3 =
                     let uu___4 =
                       FStar_Ident.string_of_lid
                         tcmod.FStar_Syntax_Syntax.name in
                     FStar_Options.dump_module uu___4 in
                   if uu___3
                   then
                     let uu___4 = FStar_Syntax_Print.modul_to_string tcmod in
                     FStar_Compiler_Util.print1
                       "Module after type checking:\n%s\n" uu___4
                   else ());
                  (let extend_tcenv tcmod1 tcenv =
                     (let uu___4 =
                        let uu___5 = FStar_Options.lax () in
                        Prims.op_Negation uu___5 in
                      if uu___4 then FStar_SMTEncoding_Z3.refresh () else ());
                     (let uu___4 =
                        let uu___5 =
                          FStar_ToSyntax_ToSyntax.add_modul_to_env tcmod1
                            tc_result.FStar_CheckedFiles.mii
                            (FStar_TypeChecker_Normalize.erase_universes
                               tcenv) in
                        FStar_Compiler_Effect.op_Less_Bar
                          (with_dsenv_of_tcenv tcenv) uu___5 in
                      match uu___4 with
                      | (uu___5, tcenv1) ->
                          let env1 =
                            FStar_TypeChecker_Tc.load_checked_module tcenv1
                              tcmod1 in
                          (maybe_restore_opts ();
                           (let uu___8 =
                              let uu___9 = FStar_Options.lax () in
                              Prims.op_Negation uu___9 in
                            if uu___8
                            then
                              FStar_SMTEncoding_Encode.encode_modul_from_cache
                                env1 tcmod1 smt_decls
                            else ());
                           ((), env1))) in
                   let env1 =
                     FStar_Profiling.profile
                       (fun uu___3 ->
                          let uu___4 =
                            with_tcenv_of_env env (extend_tcenv tcmod) in
                          FStar_Compiler_Effect.op_Bar_Greater uu___4
                            FStar_Pervasives_Native.snd)
                       FStar_Pervasives_Native.None
                       "FStar.Universal.extend_tcenv" in
                   let mllib =
                     let uu___3 = FStar_Options.codegen () in
                     match uu___3 with
                     | FStar_Pervasives_Native.None ->
                         FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some tgt ->
                         let uu___4 =
                           (let uu___5 =
                              FStar_Ident.string_of_lid
                                tcmod.FStar_Syntax_Syntax.name in
                            FStar_Options.should_extract uu___5 tgt) &&
                             ((Prims.op_Negation
                                 tcmod.FStar_Syntax_Syntax.is_interface)
                                || (tgt = FStar_Options.Krml)) in
                         if uu___4
                         then
                           let uu___5 = maybe_extract_mldefs tcmod env1 in
                           (match uu___5 with
                            | (extracted_defs, _extraction_time) ->
                                extracted_defs)
                         else FStar_Pervasives_Native.None in
                   let uu___3 = maybe_extract_ml_iface tcmod env1 in
                   match uu___3 with
                   | (env2, _time) -> (tc_result, mllib, env2)))
           else
             (let uu___3 = tc_source_file () in
              match uu___3 with
              | (tc_result, mllib, env1) -> (tc_result, mllib, env1)))
let (tc_one_file_for_ide :
  FStar_TypeChecker_Env.env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string ->
        FStar_Parser_Dep.parsing_data ->
          (FStar_CheckedFiles.tc_result * FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun pre_fn ->
      fun fn ->
        fun parsing_data ->
          let env1 = env_of_tcenv env in
          let uu___ = tc_one_file env1 pre_fn fn parsing_data in
          match uu___ with
          | (tc_result, uu___1, env2) ->
              let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env2 in
              (tc_result, uu___2)
let (needs_interleaving : Prims.string -> Prims.string -> Prims.bool) =
  fun intf ->
    fun impl ->
      let m1 = FStar_Parser_Dep.lowercase_module_name intf in
      let m2 = FStar_Parser_Dep.lowercase_module_name impl in
      ((m1 = m2) &&
         (let uu___ = FStar_Compiler_Util.get_file_extension intf in
          FStar_Compiler_List.mem uu___ ["fsti"; "fsi"]))
        &&
        (let uu___ = FStar_Compiler_Util.get_file_extension impl in
         FStar_Compiler_List.mem uu___ ["fst"; "fs"])
let (tc_one_file_from_remaining :
  Prims.string Prims.list ->
    uenv ->
      FStar_Parser_Dep.deps ->
        (Prims.string Prims.list * FStar_CheckedFiles.tc_result *
          FStar_Extraction_ML_Syntax.mllib FStar_Pervasives_Native.option *
          uenv))
  =
  fun remaining ->
    fun env ->
      fun deps ->
        let uu___ =
          match remaining with
          | intf::impl::remaining1 when needs_interleaving intf impl ->
              let uu___1 =
                let uu___2 =
                  FStar_Compiler_Effect.op_Bar_Greater impl
                    (FStar_Parser_Dep.parsing_data_of deps) in
                tc_one_file env (FStar_Pervasives_Native.Some intf) impl
                  uu___2 in
              (match uu___1 with
               | (m, mllib, env1) -> (remaining1, (m, mllib, env1)))
          | intf_or_impl::remaining1 ->
              let uu___1 =
                let uu___2 =
                  FStar_Compiler_Effect.op_Bar_Greater intf_or_impl
                    (FStar_Parser_Dep.parsing_data_of deps) in
                tc_one_file env FStar_Pervasives_Native.None intf_or_impl
                  uu___2 in
              (match uu___1 with
               | (m, mllib, env1) -> (remaining1, (m, mllib, env1)))
          | [] -> failwith "Impossible: Empty remaining modules" in
        match uu___ with
        | (remaining1, (nmods, mllib, env1)) ->
            (remaining1, nmods, mllib, env1)
let rec (tc_fold_interleave :
  FStar_Parser_Dep.deps ->
    (FStar_CheckedFiles.tc_result Prims.list *
      FStar_Extraction_ML_Syntax.mllib Prims.list * uenv) ->
      Prims.string Prims.list ->
        (FStar_CheckedFiles.tc_result Prims.list *
          FStar_Extraction_ML_Syntax.mllib Prims.list * uenv))
  =
  fun deps ->
    fun acc ->
      fun remaining ->
        let as_list uu___ =
          match uu___ with
          | FStar_Pervasives_Native.None -> []
          | FStar_Pervasives_Native.Some l -> [l] in
        match remaining with
        | [] -> acc
        | uu___ ->
            let uu___1 = acc in
            (match uu___1 with
             | (mods, mllibs, env) ->
                 let uu___2 = tc_one_file_from_remaining remaining env deps in
                 (match uu___2 with
                  | (remaining1, nmod, mllib, env1) ->
                      ((let uu___4 =
                          let uu___5 =
                            FStar_Options.profile_group_by_decls () in
                          Prims.op_Negation uu___5 in
                        if uu___4
                        then
                          let uu___5 =
                            FStar_Ident.string_of_lid
                              (nmod.FStar_CheckedFiles.checked_module).FStar_Syntax_Syntax.name in
                          FStar_Profiling.report_and_clear uu___5
                        else ());
                       tc_fold_interleave deps
                         ((FStar_Compiler_List.op_At mods [nmod]),
                           (FStar_Compiler_List.op_At mllibs (as_list mllib)),
                           env1) remaining1)))
let (batch_mode_tc :
  Prims.string Prims.list ->
    FStar_Parser_Dep.deps ->
      (FStar_CheckedFiles.tc_result Prims.list * uenv * (uenv -> uenv)))
  =
  fun filenames ->
    fun dep_graph ->
      (let uu___1 =
         FStar_Options.debug_at_level_no_module (FStar_Options.Other "Dep") in
       if uu___1
       then
         (FStar_Compiler_Util.print_endline
            "Auto-deps kicked in; here's some info.";
          FStar_Compiler_Util.print1
            "Here's the list of filenames we will process: %s\n"
            (FStar_String.concat " " filenames);
          (let uu___4 =
             let uu___5 =
               FStar_Compiler_Effect.op_Bar_Greater filenames
                 (FStar_Compiler_List.filter FStar_Options.should_verify_file) in
             FStar_String.concat " " uu___5 in
           FStar_Compiler_Util.print1
             "Here's the list of modules we will verify: %s\n" uu___4))
       else ());
      (let env =
         let uu___1 = init_env dep_graph in
         FStar_Extraction_ML_UEnv.new_uenv uu___1 in
       let uu___1 = tc_fold_interleave dep_graph ([], [], env) filenames in
       match uu___1 with
       | (all_mods, mllibs, env1) ->
           ((let uu___3 =
               let uu___4 = FStar_Errors.get_err_count () in
               uu___4 = Prims.int_zero in
             if uu___3 then emit mllibs else ());
            (let solver_refresh env2 =
               let uu___3 =
                 with_tcenv_of_env env2
                   (fun tcenv ->
                      (let uu___5 =
                         (FStar_Options.interactive ()) &&
                           (let uu___6 = FStar_Errors.get_err_count () in
                            uu___6 = Prims.int_zero) in
                       if uu___5
                       then
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                           ()
                       else
                         (tcenv.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.finish
                           ());
                      ((), tcenv)) in
               FStar_Compiler_Effect.op_Less_Bar FStar_Pervasives_Native.snd
                 uu___3 in
             (all_mods, env1, solver_refresh))))