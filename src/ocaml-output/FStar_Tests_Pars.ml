open Prims
let (test_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Test"] FStar_Compiler_Range.dummyRange
let (tcenv_ref :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (test_mod_ref :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
    FStar_Compiler_Effect.ref)
  =
  FStar_Compiler_Util.mk_ref
    (FStar_Pervasives_Native.Some
       {
         FStar_Syntax_Syntax.name = test_lid;
         FStar_Syntax_Syntax.declarations = [];
         FStar_Syntax_Syntax.is_interface = false
       })
let (parse_mod :
  Prims.string ->
    FStar_Syntax_DsEnv.env ->
      (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.modul))
  =
  fun mod_name ->
    fun dsenv ->
      let uu___ =
        FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename mod_name) in
      match uu___ with
      | FStar_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inl m, uu___1) ->
          let uu___2 =
            let uu___3 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul m in
            uu___3 dsenv in
          (match uu___2 with
           | (m1, env') ->
               let uu___3 =
                 let uu___4 =
                   FStar_Ident.lid_of_path ["Test"]
                     FStar_Compiler_Range.dummyRange in
                 FStar_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu___4 FStar_Syntax_DsEnv.default_mii in
               (match uu___3 with | (env'1, uu___4) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (err, msg, r) ->
          FStar_Compiler_Effect.raise (FStar_Errors.Error (err, msg, r, []))
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Pervasives.Inr uu___1, uu___2) ->
          let msg =
            FStar_Compiler_Util.format1 "%s: expected a module\n" mod_name in
          FStar_Errors.raise_error (FStar_Errors.Fatal_ModuleExpected, msg)
            FStar_Compiler_Range.dummyRange
      | FStar_Parser_ParseIt.Term uu___1 ->
          failwith
            "Impossible: parsing a Filename always results in an ASTFragment"
let (add_mods :
  Prims.string Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_Syntax_DsEnv.env * FStar_TypeChecker_Env.env))
  =
  fun mod_names ->
    fun dsenv ->
      fun env ->
        FStar_Compiler_List.fold_left
          (fun uu___ ->
             fun mod_name ->
               match uu___ with
               | (dsenv1, env1) ->
                   let uu___1 = parse_mod mod_name dsenv1 in
                   (match uu___1 with
                    | (dsenv2, string_mod) ->
                        let uu___2 =
                          FStar_TypeChecker_Tc.check_module env1 string_mod
                            false in
                        (match uu___2 with | (_mod, env2) -> (dsenv2, env2))))
          (dsenv, env) mod_names
let (init_once : unit -> unit) =
  fun uu___ ->
    let solver = FStar_SMTEncoding_Solver.dummy in
    let env =
      FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps
        FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term
        FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term_fastpath
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_Rel.teq_nosmt_force
        FStar_TypeChecker_Rel.subtype_nosmt_force solver
        FStar_Parser_Const.prims_lid
        FStar_TypeChecker_NBE.normalize_for_unit_test
        FStar_Universal.core_check in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let uu___2 =
       let uu___3 = FStar_Options.prims () in
       let uu___4 = FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps in
       parse_mod uu___3 uu___4 in
     match uu___2 with
     | (dsenv, prims_mod) ->
         let env1 =
           {
             FStar_TypeChecker_Env.solver =
               (env.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (env.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (env.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (env.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (env.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (env.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (env.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (env.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (env.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (env.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (env.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (env.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (env.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (env.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq_strict =
               (env.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (env.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (env.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (env.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (env.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (env.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (env.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (env.FStar_TypeChecker_Env.tc_term);
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
             FStar_TypeChecker_Env.use_bv_sorts =
               (env.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (env.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (env.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (env.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (env.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (env.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (env.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (env.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (env.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (env.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (env.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = dsenv;
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
         let uu___3 = FStar_TypeChecker_Tc.check_module env1 prims_mod false in
         (match uu___3 with
          | (_prims_mod, env2) ->
              let env3 =
                {
                  FStar_TypeChecker_Env.solver =
                    (env2.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (env2.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (env2.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (env2.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (env2.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (env2.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (env2.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (env2.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (env2.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (env2.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (env2.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (env2.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (env2.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (env2.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (env2.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (env2.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq_strict =
                    (env2.FStar_TypeChecker_Env.use_eq_strict);
                  FStar_TypeChecker_Env.is_iface =
                    (env2.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (env2.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (env2.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (env2.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (env2.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (env2.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (env2.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (env2.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (env2.FStar_TypeChecker_Env.tc_term);
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
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (env2.FStar_TypeChecker_Env.use_bv_sorts);
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
                  FStar_TypeChecker_Env.splice =
                    (env2.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (env2.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (env2.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.identifier_info =
                    (env2.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (env2.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv = dsenv;
                  FStar_TypeChecker_Env.nbe =
                    (env2.FStar_TypeChecker_Env.nbe);
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
                FStar_TypeChecker_Env.set_current_module env3 test_lid in
              FStar_Compiler_Effect.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env4)))
let (uu___52 : unit) = FStar_Main.setup_hooks (); init_once ()
let (init : unit -> FStar_TypeChecker_Env.env) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang tcenv_ref in
    match uu___1 with
    | FStar_Pervasives_Native.Some f -> f
    | uu___2 ->
        failwith
          "Should have already been initialized by the top-level effect"
let (frag_of_text : Prims.string -> FStar_Parser_ParseIt.input_frag) =
  fun s ->
    {
      FStar_Parser_ParseIt.frag_fname = " input";
      FStar_Parser_ParseIt.frag_text = s;
      FStar_Parser_ParseIt.frag_line = Prims.int_one;
      FStar_Parser_ParseIt.frag_col = Prims.int_zero
    }
let (pars : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let tcenv = init () in
             let uu___1 =
               let uu___2 =
                 FStar_Compiler_Effect.op_Less_Bar
                   (fun uu___3 -> FStar_Parser_ParseIt.Fragment uu___3)
                   (frag_of_text s) in
               FStar_Parser_ParseIt.parse uu___2 in
             (match uu___1 with
              | FStar_Parser_ParseIt.Term t ->
                  FStar_ToSyntax_ToSyntax.desugar_term
                    tcenv.FStar_TypeChecker_Env.dsenv t
              | FStar_Parser_ParseIt.ParseError (e, msg, r) ->
                  FStar_Errors.raise_error (e, msg) r
              | FStar_Parser_ParseIt.ASTFragment uu___2 ->
                  failwith
                    "Impossible: parsing a Fragment always results in a Term"))
        ()
    with
    | FStar_Errors.Error (err, msg, r, _ctx) when
        let uu___1 = FStar_Options.trace_error () in
        FStar_Compiler_Effect.op_Less_Bar Prims.op_Negation uu___1 ->
        (if r = FStar_Compiler_Range.dummyRange
         then FStar_Compiler_Util.print_string msg
         else
           (let uu___3 = FStar_Compiler_Range.string_of_range r in
            FStar_Compiler_Util.print2 "%s: %s\n" uu___3 msg);
         FStar_Compiler_Effect.exit Prims.int_one)
    | e when
        let uu___1 = FStar_Options.trace_error () in Prims.op_Negation uu___1
        -> FStar_Compiler_Effect.raise e
let (tc' :
  Prims.string ->
    (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t *
      FStar_TypeChecker_Env.env))
  =
  fun s ->
    let tm = pars s in
    let tcenv = init () in
    let tcenv1 =
      {
        FStar_TypeChecker_Env.solver = (tcenv.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (tcenv.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (tcenv.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (tcenv.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (tcenv.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (tcenv.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (tcenv.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (tcenv.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (tcenv.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (tcenv.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (tcenv.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (tcenv.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (tcenv.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (tcenv.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (tcenv.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq_strict =
          (tcenv.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (tcenv.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (tcenv.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (tcenv.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (tcenv.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (tcenv.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (tcenv.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (tcenv.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (tcenv.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (tcenv.FStar_TypeChecker_Env.tc_term);
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
        FStar_TypeChecker_Env.use_bv_sorts =
          (tcenv.FStar_TypeChecker_Env.use_bv_sorts);
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
        FStar_TypeChecker_Env.splice = (tcenv.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (tcenv.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (tcenv.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (tcenv.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (tcenv.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (tcenv.FStar_TypeChecker_Env.dsenv);
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
      } in
    let uu___ = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu___ with | (tm1, uu___1, g) -> (tm1, g, tcenv1)
let (tc : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s -> let uu___ = tc' s in match uu___ with | (tm, uu___1, uu___2) -> tm
let (tc_nbe : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    let uu___ = tc' s in
    match uu___ with
    | (tm, g, tcenv) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv g; tm)
let (tc_nbe_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun tm ->
    let tcenv = init () in
    let tcenv1 =
      {
        FStar_TypeChecker_Env.solver = (tcenv.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (tcenv.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (tcenv.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (tcenv.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (tcenv.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (tcenv.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (tcenv.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (tcenv.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (tcenv.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (tcenv.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (tcenv.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (tcenv.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (tcenv.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (tcenv.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (tcenv.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq_strict =
          (tcenv.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (tcenv.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (tcenv.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (tcenv.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (tcenv.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (tcenv.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (tcenv.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (tcenv.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (tcenv.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (tcenv.FStar_TypeChecker_Env.tc_term);
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
        FStar_TypeChecker_Env.use_bv_sorts =
          (tcenv.FStar_TypeChecker_Env.use_bv_sorts);
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
        FStar_TypeChecker_Env.splice = (tcenv.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (tcenv.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (tcenv.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (tcenv.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (tcenv.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (tcenv.FStar_TypeChecker_Env.dsenv);
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
      } in
    let uu___ = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu___ with
    | (tm1, uu___1, g) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g; tm1)
let (pars_and_tc_fragment : Prims.string -> unit) =
  fun s ->
    FStar_Options.set_option "trace_error" (FStar_Options.Bool true);
    (let report uu___1 =
       let uu___2 = FStar_Errors.report_all () in
       FStar_Compiler_Effect.op_Bar_Greater uu___2 (fun uu___3 -> ()) in
     try
       (fun uu___1 ->
          match () with
          | () ->
              let tcenv = init () in
              let frag = frag_of_text s in
              (try
                 (fun uu___2 ->
                    match () with
                    | () ->
                        let uu___3 =
                          let uu___4 =
                            FStar_Compiler_Effect.op_Bang test_mod_ref in
                          FStar_Universal.tc_one_fragment uu___4 tcenv frag in
                        (match uu___3 with
                         | (test_mod', tcenv') ->
                             (FStar_Compiler_Effect.op_Colon_Equals
                                test_mod_ref test_mod';
                              FStar_Compiler_Effect.op_Colon_Equals tcenv_ref
                                (FStar_Pervasives_Native.Some tcenv');
                              (let n = FStar_Errors.get_err_count () in
                               if n <> Prims.int_zero
                               then
                                 (report ();
                                  (let uu___7 =
                                     let uu___8 =
                                       let uu___9 =
                                         FStar_Compiler_Util.string_of_int n in
                                       FStar_Compiler_Util.format1
                                         "%s errors were reported" uu___9 in
                                     (FStar_Errors.Fatal_ErrorsReported,
                                       uu___8) in
                                   FStar_Errors.raise_err uu___7))
                               else ())))) ()
               with
               | uu___2 ->
                   (report ();
                    FStar_Errors.raise_err
                      (FStar_Errors.Fatal_TcOneFragmentFailed,
                        (Prims.op_Hat "tc_one_fragment failed: " s))))) ()
     with
     | uu___1 ->
         if
           let uu___2 = FStar_Options.trace_error () in
           Prims.op_Negation uu___2
         then Obj.magic (Obj.repr (FStar_Compiler_Effect.raise uu___1))
         else Obj.magic (Obj.repr (failwith "unreachable")))