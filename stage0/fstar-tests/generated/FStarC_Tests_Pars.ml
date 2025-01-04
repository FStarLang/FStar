open Prims
let (test_lid : FStarC_Ident.lident) =
  FStarC_Ident.lid_of_path ["Test"] FStarC_Compiler_Range_Type.dummyRange
let (tcenv_ref :
  FStarC_TypeChecker_Env.env FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (test_mod_ref :
  FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  =
  FStarC_Compiler_Util.mk_ref
    (FStar_Pervasives_Native.Some
       {
         FStarC_Syntax_Syntax.name = test_lid;
         FStarC_Syntax_Syntax.declarations = [];
         FStarC_Syntax_Syntax.is_interface = false
       })
let (parse_mod :
  Prims.string ->
    FStarC_Syntax_DsEnv.env ->
      (FStarC_Syntax_DsEnv.env * FStarC_Syntax_Syntax.modul))
  =
  fun mod_name ->
    fun dsenv ->
      let uu___ =
        FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None
          (FStarC_Parser_ParseIt.Filename mod_name) in
      match uu___ with
      | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inl m, uu___1) ->
          let uu___2 =
            let uu___3 = FStarC_ToSyntax_ToSyntax.ast_modul_to_modul m in
            uu___3 dsenv in
          (match uu___2 with
           | (m1, env') ->
               let uu___3 =
                 let uu___4 =
                   FStarC_Ident.lid_of_path ["Test"]
                     FStarC_Compiler_Range_Type.dummyRange in
                 FStarC_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu___4 FStarC_Syntax_DsEnv.default_mii in
               (match uu___3 with | (env'1, uu___4) -> (env'1, m1)))
      | FStarC_Parser_ParseIt.ParseError (err, msg, r) ->
          FStarC_Compiler_Effect.raise
            (FStarC_Errors.Error (err, msg, r, []))
      | FStarC_Parser_ParseIt.ASTFragment
          (FStar_Pervasives.Inr uu___1, uu___2) ->
          let msg =
            FStarC_Compiler_Util.format1 "%s: expected a module\n" mod_name in
          FStarC_Errors.raise_error0 FStarC_Errors_Codes.Fatal_ModuleExpected
            () (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic msg)
      | FStarC_Parser_ParseIt.Term uu___1 ->
          failwith
            "Impossible: parsing a Filename always results in an ASTFragment"
let (add_mods :
  Prims.string Prims.list ->
    FStarC_Syntax_DsEnv.env ->
      FStarC_TypeChecker_Env.env ->
        (FStarC_Syntax_DsEnv.env * FStarC_TypeChecker_Env.env))
  =
  fun mod_names ->
    fun dsenv ->
      fun env ->
        FStarC_Compiler_List.fold_left
          (fun uu___ ->
             fun mod_name ->
               match uu___ with
               | (dsenv1, env1) ->
                   let uu___1 = parse_mod mod_name dsenv1 in
                   (match uu___1 with
                    | (dsenv2, string_mod) ->
                        let uu___2 =
                          FStarC_TypeChecker_Tc.check_module env1 string_mod
                            false in
                        (match uu___2 with | (_mod, env2) -> (dsenv2, env2))))
          (dsenv, env) mod_names
let (init_once : unit -> unit) =
  fun uu___ ->
    let solver = FStarC_SMTEncoding_Solver.dummy in
    let env =
      FStarC_TypeChecker_Env.initial_env FStarC_Parser_Dep.empty_deps
        FStarC_TypeChecker_TcTerm.tc_term
        FStarC_TypeChecker_TcTerm.typeof_tot_or_gtot_term
        FStarC_TypeChecker_TcTerm.typeof_tot_or_gtot_term_fastpath
        FStarC_TypeChecker_TcTerm.universe_of
        FStarC_TypeChecker_Rel.teq_nosmt_force
        FStarC_TypeChecker_Rel.subtype_nosmt_force solver
        FStarC_Parser_Const.prims_lid
        FStarC_TypeChecker_NBE.normalize_for_unit_test
        FStarC_Universal.core_check in
    (env.FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.init env;
    (let uu___2 =
       let uu___3 = FStarC_Basefiles.prims () in
       let uu___4 =
         FStarC_Syntax_DsEnv.empty_env FStarC_Parser_Dep.empty_deps in
       parse_mod uu___3 uu___4 in
     match uu___2 with
     | (dsenv, prims_mod) ->
         let env1 =
           {
             FStarC_TypeChecker_Env.solver =
               (env.FStarC_TypeChecker_Env.solver);
             FStarC_TypeChecker_Env.range =
               (env.FStarC_TypeChecker_Env.range);
             FStarC_TypeChecker_Env.curmodule =
               (env.FStarC_TypeChecker_Env.curmodule);
             FStarC_TypeChecker_Env.gamma =
               (env.FStarC_TypeChecker_Env.gamma);
             FStarC_TypeChecker_Env.gamma_sig =
               (env.FStarC_TypeChecker_Env.gamma_sig);
             FStarC_TypeChecker_Env.gamma_cache =
               (env.FStarC_TypeChecker_Env.gamma_cache);
             FStarC_TypeChecker_Env.modules =
               (env.FStarC_TypeChecker_Env.modules);
             FStarC_TypeChecker_Env.expected_typ =
               (env.FStarC_TypeChecker_Env.expected_typ);
             FStarC_TypeChecker_Env.sigtab =
               (env.FStarC_TypeChecker_Env.sigtab);
             FStarC_TypeChecker_Env.attrtab =
               (env.FStarC_TypeChecker_Env.attrtab);
             FStarC_TypeChecker_Env.instantiate_imp =
               (env.FStarC_TypeChecker_Env.instantiate_imp);
             FStarC_TypeChecker_Env.effects =
               (env.FStarC_TypeChecker_Env.effects);
             FStarC_TypeChecker_Env.generalize =
               (env.FStarC_TypeChecker_Env.generalize);
             FStarC_TypeChecker_Env.letrecs =
               (env.FStarC_TypeChecker_Env.letrecs);
             FStarC_TypeChecker_Env.top_level =
               (env.FStarC_TypeChecker_Env.top_level);
             FStarC_TypeChecker_Env.check_uvars =
               (env.FStarC_TypeChecker_Env.check_uvars);
             FStarC_TypeChecker_Env.use_eq_strict =
               (env.FStarC_TypeChecker_Env.use_eq_strict);
             FStarC_TypeChecker_Env.is_iface =
               (env.FStarC_TypeChecker_Env.is_iface);
             FStarC_TypeChecker_Env.admit =
               (env.FStarC_TypeChecker_Env.admit);
             FStarC_TypeChecker_Env.lax_universes =
               (env.FStarC_TypeChecker_Env.lax_universes);
             FStarC_TypeChecker_Env.phase1 =
               (env.FStarC_TypeChecker_Env.phase1);
             FStarC_TypeChecker_Env.failhard =
               (env.FStarC_TypeChecker_Env.failhard);
             FStarC_TypeChecker_Env.flychecking =
               (env.FStarC_TypeChecker_Env.flychecking);
             FStarC_TypeChecker_Env.uvar_subtyping =
               (env.FStarC_TypeChecker_Env.uvar_subtyping);
             FStarC_TypeChecker_Env.intactics =
               (env.FStarC_TypeChecker_Env.intactics);
             FStarC_TypeChecker_Env.nocoerce =
               (env.FStarC_TypeChecker_Env.nocoerce);
             FStarC_TypeChecker_Env.tc_term =
               (env.FStarC_TypeChecker_Env.tc_term);
             FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
               (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
             FStarC_TypeChecker_Env.universe_of =
               (env.FStarC_TypeChecker_Env.universe_of);
             FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
               (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
             FStarC_TypeChecker_Env.teq_nosmt_force =
               (env.FStarC_TypeChecker_Env.teq_nosmt_force);
             FStarC_TypeChecker_Env.subtype_nosmt_force =
               (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
             FStarC_TypeChecker_Env.qtbl_name_and_index =
               (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
             FStarC_TypeChecker_Env.normalized_eff_names =
               (env.FStarC_TypeChecker_Env.normalized_eff_names);
             FStarC_TypeChecker_Env.fv_delta_depths =
               (env.FStarC_TypeChecker_Env.fv_delta_depths);
             FStarC_TypeChecker_Env.proof_ns =
               (env.FStarC_TypeChecker_Env.proof_ns);
             FStarC_TypeChecker_Env.synth_hook =
               (env.FStarC_TypeChecker_Env.synth_hook);
             FStarC_TypeChecker_Env.try_solve_implicits_hook =
               (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
             FStarC_TypeChecker_Env.splice =
               (env.FStarC_TypeChecker_Env.splice);
             FStarC_TypeChecker_Env.mpreprocess =
               (env.FStarC_TypeChecker_Env.mpreprocess);
             FStarC_TypeChecker_Env.postprocess =
               (env.FStarC_TypeChecker_Env.postprocess);
             FStarC_TypeChecker_Env.identifier_info =
               (env.FStarC_TypeChecker_Env.identifier_info);
             FStarC_TypeChecker_Env.tc_hooks =
               (env.FStarC_TypeChecker_Env.tc_hooks);
             FStarC_TypeChecker_Env.dsenv = dsenv;
             FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
             FStarC_TypeChecker_Env.strict_args_tab =
               (env.FStarC_TypeChecker_Env.strict_args_tab);
             FStarC_TypeChecker_Env.erasable_types_tab =
               (env.FStarC_TypeChecker_Env.erasable_types_tab);
             FStarC_TypeChecker_Env.enable_defer_to_tac =
               (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
             FStarC_TypeChecker_Env.unif_allow_ref_guards =
               (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
             FStarC_TypeChecker_Env.erase_erasable_args =
               (env.FStarC_TypeChecker_Env.erase_erasable_args);
             FStarC_TypeChecker_Env.core_check =
               (env.FStarC_TypeChecker_Env.core_check);
             FStarC_TypeChecker_Env.missing_decl =
               (env.FStarC_TypeChecker_Env.missing_decl)
           } in
         let uu___3 = FStarC_TypeChecker_Tc.check_module env1 prims_mod false in
         (match uu___3 with
          | (_prims_mod, env2) ->
              let env3 =
                {
                  FStarC_TypeChecker_Env.solver =
                    (env2.FStarC_TypeChecker_Env.solver);
                  FStarC_TypeChecker_Env.range =
                    (env2.FStarC_TypeChecker_Env.range);
                  FStarC_TypeChecker_Env.curmodule =
                    (env2.FStarC_TypeChecker_Env.curmodule);
                  FStarC_TypeChecker_Env.gamma =
                    (env2.FStarC_TypeChecker_Env.gamma);
                  FStarC_TypeChecker_Env.gamma_sig =
                    (env2.FStarC_TypeChecker_Env.gamma_sig);
                  FStarC_TypeChecker_Env.gamma_cache =
                    (env2.FStarC_TypeChecker_Env.gamma_cache);
                  FStarC_TypeChecker_Env.modules =
                    (env2.FStarC_TypeChecker_Env.modules);
                  FStarC_TypeChecker_Env.expected_typ =
                    (env2.FStarC_TypeChecker_Env.expected_typ);
                  FStarC_TypeChecker_Env.sigtab =
                    (env2.FStarC_TypeChecker_Env.sigtab);
                  FStarC_TypeChecker_Env.attrtab =
                    (env2.FStarC_TypeChecker_Env.attrtab);
                  FStarC_TypeChecker_Env.instantiate_imp =
                    (env2.FStarC_TypeChecker_Env.instantiate_imp);
                  FStarC_TypeChecker_Env.effects =
                    (env2.FStarC_TypeChecker_Env.effects);
                  FStarC_TypeChecker_Env.generalize =
                    (env2.FStarC_TypeChecker_Env.generalize);
                  FStarC_TypeChecker_Env.letrecs =
                    (env2.FStarC_TypeChecker_Env.letrecs);
                  FStarC_TypeChecker_Env.top_level =
                    (env2.FStarC_TypeChecker_Env.top_level);
                  FStarC_TypeChecker_Env.check_uvars =
                    (env2.FStarC_TypeChecker_Env.check_uvars);
                  FStarC_TypeChecker_Env.use_eq_strict =
                    (env2.FStarC_TypeChecker_Env.use_eq_strict);
                  FStarC_TypeChecker_Env.is_iface =
                    (env2.FStarC_TypeChecker_Env.is_iface);
                  FStarC_TypeChecker_Env.admit =
                    (env2.FStarC_TypeChecker_Env.admit);
                  FStarC_TypeChecker_Env.lax_universes =
                    (env2.FStarC_TypeChecker_Env.lax_universes);
                  FStarC_TypeChecker_Env.phase1 =
                    (env2.FStarC_TypeChecker_Env.phase1);
                  FStarC_TypeChecker_Env.failhard =
                    (env2.FStarC_TypeChecker_Env.failhard);
                  FStarC_TypeChecker_Env.flychecking =
                    (env2.FStarC_TypeChecker_Env.flychecking);
                  FStarC_TypeChecker_Env.uvar_subtyping =
                    (env2.FStarC_TypeChecker_Env.uvar_subtyping);
                  FStarC_TypeChecker_Env.intactics =
                    (env2.FStarC_TypeChecker_Env.intactics);
                  FStarC_TypeChecker_Env.nocoerce =
                    (env2.FStarC_TypeChecker_Env.nocoerce);
                  FStarC_TypeChecker_Env.tc_term =
                    (env2.FStarC_TypeChecker_Env.tc_term);
                  FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                    (env2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                  FStarC_TypeChecker_Env.universe_of =
                    (env2.FStarC_TypeChecker_Env.universe_of);
                  FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                    (env2.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                  FStarC_TypeChecker_Env.teq_nosmt_force =
                    (env2.FStarC_TypeChecker_Env.teq_nosmt_force);
                  FStarC_TypeChecker_Env.subtype_nosmt_force =
                    (env2.FStarC_TypeChecker_Env.subtype_nosmt_force);
                  FStarC_TypeChecker_Env.qtbl_name_and_index =
                    (env2.FStarC_TypeChecker_Env.qtbl_name_and_index);
                  FStarC_TypeChecker_Env.normalized_eff_names =
                    (env2.FStarC_TypeChecker_Env.normalized_eff_names);
                  FStarC_TypeChecker_Env.fv_delta_depths =
                    (env2.FStarC_TypeChecker_Env.fv_delta_depths);
                  FStarC_TypeChecker_Env.proof_ns =
                    (env2.FStarC_TypeChecker_Env.proof_ns);
                  FStarC_TypeChecker_Env.synth_hook =
                    (env2.FStarC_TypeChecker_Env.synth_hook);
                  FStarC_TypeChecker_Env.try_solve_implicits_hook =
                    (env2.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                  FStarC_TypeChecker_Env.splice =
                    (env2.FStarC_TypeChecker_Env.splice);
                  FStarC_TypeChecker_Env.mpreprocess =
                    (env2.FStarC_TypeChecker_Env.mpreprocess);
                  FStarC_TypeChecker_Env.postprocess =
                    (env2.FStarC_TypeChecker_Env.postprocess);
                  FStarC_TypeChecker_Env.identifier_info =
                    (env2.FStarC_TypeChecker_Env.identifier_info);
                  FStarC_TypeChecker_Env.tc_hooks =
                    (env2.FStarC_TypeChecker_Env.tc_hooks);
                  FStarC_TypeChecker_Env.dsenv = dsenv;
                  FStarC_TypeChecker_Env.nbe =
                    (env2.FStarC_TypeChecker_Env.nbe);
                  FStarC_TypeChecker_Env.strict_args_tab =
                    (env2.FStarC_TypeChecker_Env.strict_args_tab);
                  FStarC_TypeChecker_Env.erasable_types_tab =
                    (env2.FStarC_TypeChecker_Env.erasable_types_tab);
                  FStarC_TypeChecker_Env.enable_defer_to_tac =
                    (env2.FStarC_TypeChecker_Env.enable_defer_to_tac);
                  FStarC_TypeChecker_Env.unif_allow_ref_guards =
                    (env2.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                  FStarC_TypeChecker_Env.erase_erasable_args =
                    (env2.FStarC_TypeChecker_Env.erase_erasable_args);
                  FStarC_TypeChecker_Env.core_check =
                    (env2.FStarC_TypeChecker_Env.core_check);
                  FStarC_TypeChecker_Env.missing_decl =
                    (env2.FStarC_TypeChecker_Env.missing_decl)
                } in
              let env4 =
                FStarC_TypeChecker_Env.set_current_module env3 test_lid in
              FStarC_Compiler_Effect.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env4)))
let (uu___0 : unit) = FStarC_Main.setup_hooks (); init_once ()
let (init : unit -> FStarC_TypeChecker_Env.env) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang tcenv_ref in
    match uu___1 with
    | FStar_Pervasives_Native.Some f -> f
    | uu___2 ->
        failwith
          "Should have already been initialized by the top-level effect"
let (frag_of_text : Prims.string -> FStarC_Parser_ParseIt.input_frag) =
  fun s ->
    {
      FStarC_Parser_ParseIt.frag_fname = " input";
      FStarC_Parser_ParseIt.frag_text = s;
      FStarC_Parser_ParseIt.frag_line = Prims.int_one;
      FStarC_Parser_ParseIt.frag_col = Prims.int_zero
    }
let (pars : Prims.string -> FStarC_Syntax_Syntax.term) =
  fun s ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let tcenv = init () in
             let uu___1 =
               FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None
                 (FStarC_Parser_ParseIt.Fragment (frag_of_text s)) in
             (match uu___1 with
              | FStarC_Parser_ParseIt.Term t ->
                  FStarC_ToSyntax_ToSyntax.desugar_term
                    tcenv.FStarC_TypeChecker_Env.dsenv t
              | FStarC_Parser_ParseIt.ParseError (e, msg, r) ->
                  FStarC_Errors.raise_error
                    FStarC_Class_HasRange.hasRange_range r e ()
                    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic msg)
              | FStarC_Parser_ParseIt.ASTFragment uu___2 ->
                  failwith
                    "Impossible: parsing a Fragment always results in a Term"))
        ()
    with
    | FStarC_Errors.Error (err, msg, r, _ctx) when
        let uu___1 = FStarC_Options.trace_error () in
        Prims.op_Negation uu___1 ->
        (if r = FStarC_Compiler_Range_Type.dummyRange
         then
           (let uu___2 = FStarC_Errors_Msg.rendermsg msg in
            FStarC_Compiler_Util.print_string uu___2)
         else
           (let uu___3 = FStarC_Compiler_Range_Ops.string_of_range r in
            let uu___4 = FStarC_Errors_Msg.rendermsg msg in
            FStarC_Compiler_Util.print2 "%s: %s\n" uu___3 uu___4);
         FStarC_Compiler_Effect.exit Prims.int_one)
    | e when
        let uu___1 = FStarC_Options.trace_error () in
        Prims.op_Negation uu___1 -> FStarC_Compiler_Effect.raise e
let (tc' :
  Prims.string -> (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Env.env)) =
  fun s ->
    let tm = pars s in
    let tcenv = init () in
    let tcenv1 =
      {
        FStarC_TypeChecker_Env.solver = (tcenv.FStarC_TypeChecker_Env.solver);
        FStarC_TypeChecker_Env.range = (tcenv.FStarC_TypeChecker_Env.range);
        FStarC_TypeChecker_Env.curmodule =
          (tcenv.FStarC_TypeChecker_Env.curmodule);
        FStarC_TypeChecker_Env.gamma = (tcenv.FStarC_TypeChecker_Env.gamma);
        FStarC_TypeChecker_Env.gamma_sig =
          (tcenv.FStarC_TypeChecker_Env.gamma_sig);
        FStarC_TypeChecker_Env.gamma_cache =
          (tcenv.FStarC_TypeChecker_Env.gamma_cache);
        FStarC_TypeChecker_Env.modules =
          (tcenv.FStarC_TypeChecker_Env.modules);
        FStarC_TypeChecker_Env.expected_typ =
          (tcenv.FStarC_TypeChecker_Env.expected_typ);
        FStarC_TypeChecker_Env.sigtab = (tcenv.FStarC_TypeChecker_Env.sigtab);
        FStarC_TypeChecker_Env.attrtab =
          (tcenv.FStarC_TypeChecker_Env.attrtab);
        FStarC_TypeChecker_Env.instantiate_imp =
          (tcenv.FStarC_TypeChecker_Env.instantiate_imp);
        FStarC_TypeChecker_Env.effects =
          (tcenv.FStarC_TypeChecker_Env.effects);
        FStarC_TypeChecker_Env.generalize =
          (tcenv.FStarC_TypeChecker_Env.generalize);
        FStarC_TypeChecker_Env.letrecs =
          (tcenv.FStarC_TypeChecker_Env.letrecs);
        FStarC_TypeChecker_Env.top_level = false;
        FStarC_TypeChecker_Env.check_uvars =
          (tcenv.FStarC_TypeChecker_Env.check_uvars);
        FStarC_TypeChecker_Env.use_eq_strict =
          (tcenv.FStarC_TypeChecker_Env.use_eq_strict);
        FStarC_TypeChecker_Env.is_iface =
          (tcenv.FStarC_TypeChecker_Env.is_iface);
        FStarC_TypeChecker_Env.admit = (tcenv.FStarC_TypeChecker_Env.admit);
        FStarC_TypeChecker_Env.lax_universes =
          (tcenv.FStarC_TypeChecker_Env.lax_universes);
        FStarC_TypeChecker_Env.phase1 = true;
        FStarC_TypeChecker_Env.failhard =
          (tcenv.FStarC_TypeChecker_Env.failhard);
        FStarC_TypeChecker_Env.flychecking =
          (tcenv.FStarC_TypeChecker_Env.flychecking);
        FStarC_TypeChecker_Env.uvar_subtyping =
          (tcenv.FStarC_TypeChecker_Env.uvar_subtyping);
        FStarC_TypeChecker_Env.intactics =
          (tcenv.FStarC_TypeChecker_Env.intactics);
        FStarC_TypeChecker_Env.nocoerce =
          (tcenv.FStarC_TypeChecker_Env.nocoerce);
        FStarC_TypeChecker_Env.tc_term =
          (tcenv.FStarC_TypeChecker_Env.tc_term);
        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
          (tcenv.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStarC_TypeChecker_Env.universe_of =
          (tcenv.FStarC_TypeChecker_Env.universe_of);
        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (tcenv.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStarC_TypeChecker_Env.teq_nosmt_force =
          (tcenv.FStarC_TypeChecker_Env.teq_nosmt_force);
        FStarC_TypeChecker_Env.subtype_nosmt_force =
          (tcenv.FStarC_TypeChecker_Env.subtype_nosmt_force);
        FStarC_TypeChecker_Env.qtbl_name_and_index =
          (tcenv.FStarC_TypeChecker_Env.qtbl_name_and_index);
        FStarC_TypeChecker_Env.normalized_eff_names =
          (tcenv.FStarC_TypeChecker_Env.normalized_eff_names);
        FStarC_TypeChecker_Env.fv_delta_depths =
          (tcenv.FStarC_TypeChecker_Env.fv_delta_depths);
        FStarC_TypeChecker_Env.proof_ns =
          (tcenv.FStarC_TypeChecker_Env.proof_ns);
        FStarC_TypeChecker_Env.synth_hook =
          (tcenv.FStarC_TypeChecker_Env.synth_hook);
        FStarC_TypeChecker_Env.try_solve_implicits_hook =
          (tcenv.FStarC_TypeChecker_Env.try_solve_implicits_hook);
        FStarC_TypeChecker_Env.splice = (tcenv.FStarC_TypeChecker_Env.splice);
        FStarC_TypeChecker_Env.mpreprocess =
          (tcenv.FStarC_TypeChecker_Env.mpreprocess);
        FStarC_TypeChecker_Env.postprocess =
          (tcenv.FStarC_TypeChecker_Env.postprocess);
        FStarC_TypeChecker_Env.identifier_info =
          (tcenv.FStarC_TypeChecker_Env.identifier_info);
        FStarC_TypeChecker_Env.tc_hooks =
          (tcenv.FStarC_TypeChecker_Env.tc_hooks);
        FStarC_TypeChecker_Env.dsenv = (tcenv.FStarC_TypeChecker_Env.dsenv);
        FStarC_TypeChecker_Env.nbe = (tcenv.FStarC_TypeChecker_Env.nbe);
        FStarC_TypeChecker_Env.strict_args_tab =
          (tcenv.FStarC_TypeChecker_Env.strict_args_tab);
        FStarC_TypeChecker_Env.erasable_types_tab =
          (tcenv.FStarC_TypeChecker_Env.erasable_types_tab);
        FStarC_TypeChecker_Env.enable_defer_to_tac =
          (tcenv.FStarC_TypeChecker_Env.enable_defer_to_tac);
        FStarC_TypeChecker_Env.unif_allow_ref_guards =
          (tcenv.FStarC_TypeChecker_Env.unif_allow_ref_guards);
        FStarC_TypeChecker_Env.erase_erasable_args =
          (tcenv.FStarC_TypeChecker_Env.erase_erasable_args);
        FStarC_TypeChecker_Env.core_check =
          (tcenv.FStarC_TypeChecker_Env.core_check);
        FStarC_TypeChecker_Env.missing_decl =
          (tcenv.FStarC_TypeChecker_Env.missing_decl)
      } in
    let uu___ = FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu___ with
    | (tm1, uu___1, g) ->
        (FStarC_TypeChecker_Rel.force_trivial_guard tcenv1 g;
         (let tm2 = FStarC_Syntax_Compress.deep_compress false false tm1 in
          (tm2, tcenv1)))
let (tc : Prims.string -> FStarC_Syntax_Syntax.term) =
  fun s -> let uu___ = tc' s in match uu___ with | (tm, uu___1) -> tm
let (tc_term : FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun tm ->
    let tcenv = init () in
    let tcenv1 =
      {
        FStarC_TypeChecker_Env.solver = (tcenv.FStarC_TypeChecker_Env.solver);
        FStarC_TypeChecker_Env.range = (tcenv.FStarC_TypeChecker_Env.range);
        FStarC_TypeChecker_Env.curmodule =
          (tcenv.FStarC_TypeChecker_Env.curmodule);
        FStarC_TypeChecker_Env.gamma = (tcenv.FStarC_TypeChecker_Env.gamma);
        FStarC_TypeChecker_Env.gamma_sig =
          (tcenv.FStarC_TypeChecker_Env.gamma_sig);
        FStarC_TypeChecker_Env.gamma_cache =
          (tcenv.FStarC_TypeChecker_Env.gamma_cache);
        FStarC_TypeChecker_Env.modules =
          (tcenv.FStarC_TypeChecker_Env.modules);
        FStarC_TypeChecker_Env.expected_typ =
          (tcenv.FStarC_TypeChecker_Env.expected_typ);
        FStarC_TypeChecker_Env.sigtab = (tcenv.FStarC_TypeChecker_Env.sigtab);
        FStarC_TypeChecker_Env.attrtab =
          (tcenv.FStarC_TypeChecker_Env.attrtab);
        FStarC_TypeChecker_Env.instantiate_imp =
          (tcenv.FStarC_TypeChecker_Env.instantiate_imp);
        FStarC_TypeChecker_Env.effects =
          (tcenv.FStarC_TypeChecker_Env.effects);
        FStarC_TypeChecker_Env.generalize =
          (tcenv.FStarC_TypeChecker_Env.generalize);
        FStarC_TypeChecker_Env.letrecs =
          (tcenv.FStarC_TypeChecker_Env.letrecs);
        FStarC_TypeChecker_Env.top_level = false;
        FStarC_TypeChecker_Env.check_uvars =
          (tcenv.FStarC_TypeChecker_Env.check_uvars);
        FStarC_TypeChecker_Env.use_eq_strict =
          (tcenv.FStarC_TypeChecker_Env.use_eq_strict);
        FStarC_TypeChecker_Env.is_iface =
          (tcenv.FStarC_TypeChecker_Env.is_iface);
        FStarC_TypeChecker_Env.admit = (tcenv.FStarC_TypeChecker_Env.admit);
        FStarC_TypeChecker_Env.lax_universes =
          (tcenv.FStarC_TypeChecker_Env.lax_universes);
        FStarC_TypeChecker_Env.phase1 = (tcenv.FStarC_TypeChecker_Env.phase1);
        FStarC_TypeChecker_Env.failhard =
          (tcenv.FStarC_TypeChecker_Env.failhard);
        FStarC_TypeChecker_Env.flychecking =
          (tcenv.FStarC_TypeChecker_Env.flychecking);
        FStarC_TypeChecker_Env.uvar_subtyping =
          (tcenv.FStarC_TypeChecker_Env.uvar_subtyping);
        FStarC_TypeChecker_Env.intactics =
          (tcenv.FStarC_TypeChecker_Env.intactics);
        FStarC_TypeChecker_Env.nocoerce =
          (tcenv.FStarC_TypeChecker_Env.nocoerce);
        FStarC_TypeChecker_Env.tc_term =
          (tcenv.FStarC_TypeChecker_Env.tc_term);
        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
          (tcenv.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStarC_TypeChecker_Env.universe_of =
          (tcenv.FStarC_TypeChecker_Env.universe_of);
        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (tcenv.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStarC_TypeChecker_Env.teq_nosmt_force =
          (tcenv.FStarC_TypeChecker_Env.teq_nosmt_force);
        FStarC_TypeChecker_Env.subtype_nosmt_force =
          (tcenv.FStarC_TypeChecker_Env.subtype_nosmt_force);
        FStarC_TypeChecker_Env.qtbl_name_and_index =
          (tcenv.FStarC_TypeChecker_Env.qtbl_name_and_index);
        FStarC_TypeChecker_Env.normalized_eff_names =
          (tcenv.FStarC_TypeChecker_Env.normalized_eff_names);
        FStarC_TypeChecker_Env.fv_delta_depths =
          (tcenv.FStarC_TypeChecker_Env.fv_delta_depths);
        FStarC_TypeChecker_Env.proof_ns =
          (tcenv.FStarC_TypeChecker_Env.proof_ns);
        FStarC_TypeChecker_Env.synth_hook =
          (tcenv.FStarC_TypeChecker_Env.synth_hook);
        FStarC_TypeChecker_Env.try_solve_implicits_hook =
          (tcenv.FStarC_TypeChecker_Env.try_solve_implicits_hook);
        FStarC_TypeChecker_Env.splice = (tcenv.FStarC_TypeChecker_Env.splice);
        FStarC_TypeChecker_Env.mpreprocess =
          (tcenv.FStarC_TypeChecker_Env.mpreprocess);
        FStarC_TypeChecker_Env.postprocess =
          (tcenv.FStarC_TypeChecker_Env.postprocess);
        FStarC_TypeChecker_Env.identifier_info =
          (tcenv.FStarC_TypeChecker_Env.identifier_info);
        FStarC_TypeChecker_Env.tc_hooks =
          (tcenv.FStarC_TypeChecker_Env.tc_hooks);
        FStarC_TypeChecker_Env.dsenv = (tcenv.FStarC_TypeChecker_Env.dsenv);
        FStarC_TypeChecker_Env.nbe = (tcenv.FStarC_TypeChecker_Env.nbe);
        FStarC_TypeChecker_Env.strict_args_tab =
          (tcenv.FStarC_TypeChecker_Env.strict_args_tab);
        FStarC_TypeChecker_Env.erasable_types_tab =
          (tcenv.FStarC_TypeChecker_Env.erasable_types_tab);
        FStarC_TypeChecker_Env.enable_defer_to_tac =
          (tcenv.FStarC_TypeChecker_Env.enable_defer_to_tac);
        FStarC_TypeChecker_Env.unif_allow_ref_guards =
          (tcenv.FStarC_TypeChecker_Env.unif_allow_ref_guards);
        FStarC_TypeChecker_Env.erase_erasable_args =
          (tcenv.FStarC_TypeChecker_Env.erase_erasable_args);
        FStarC_TypeChecker_Env.core_check =
          (tcenv.FStarC_TypeChecker_Env.core_check);
        FStarC_TypeChecker_Env.missing_decl =
          (tcenv.FStarC_TypeChecker_Env.missing_decl)
      } in
    let uu___ = FStarC_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu___ with
    | (tm1, uu___1, g) ->
        (FStarC_TypeChecker_Rel.force_trivial_guard tcenv1 g;
         (let tm2 = FStarC_Syntax_Compress.deep_compress false false tm1 in
          tm2))
let (pars_and_tc_fragment : Prims.string -> unit) =
  fun s ->
    FStarC_Options.set_option "trace_error" (FStarC_Options.Bool true);
    (let report uu___1 = let uu___2 = FStarC_Errors.report_all () in () in
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
                            FStarC_Compiler_Effect.op_Bang test_mod_ref in
                          FStarC_Universal.tc_one_fragment uu___4 tcenv
                            (FStar_Pervasives.Inl (frag, [])) in
                        (match uu___3 with
                         | (test_mod', tcenv', uu___4) ->
                             (FStarC_Compiler_Effect.op_Colon_Equals
                                test_mod_ref test_mod';
                              FStarC_Compiler_Effect.op_Colon_Equals
                                tcenv_ref
                                (FStar_Pervasives_Native.Some tcenv');
                              (let n = FStarC_Errors.get_err_count () in
                               if n <> Prims.int_zero
                               then
                                 (report ();
                                  (let uu___8 =
                                     let uu___9 =
                                       FStarC_Compiler_Util.string_of_int n in
                                     FStarC_Compiler_Util.format1
                                       "%s errors were reported" uu___9 in
                                   FStarC_Errors.raise_error0
                                     FStarC_Errors_Codes.Fatal_ErrorsReported
                                     ()
                                     (Obj.magic
                                        FStarC_Errors_Msg.is_error_message_string)
                                     (Obj.magic uu___8)))
                               else ())))) ()
               with
               | uu___2 ->
                   (report ();
                    FStarC_Errors.raise_error0
                      FStarC_Errors_Codes.Fatal_TcOneFragmentFailed ()
                      (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                      (Obj.magic (Prims.strcat "tc_one_fragment failed: " s)))))
         ()
     with
     | uu___1 ->
         ((fun uu___1 ->
             if
               let uu___2 = FStarC_Options.trace_error () in
               Prims.op_Negation uu___2
             then Obj.magic (Obj.repr (FStarC_Compiler_Effect.raise uu___1))
             else Obj.magic (Obj.repr (failwith "unreachable")))) uu___1)
let (test_hashes : unit -> unit) =
  fun uu___ ->
    (let uu___2 = FStarC_Main.process_args () in ());
    pars_and_tc_fragment "type unary_nat = | U0 | US of unary_nat";
    (let test_one_hash n =
       let rec aux n1 =
         if n1 = Prims.int_zero
         then "U0"
         else
           (let uu___4 =
              let uu___5 = aux (n1 - Prims.int_one) in
              Prims.strcat uu___5 ")" in
            Prims.strcat "(US " uu___4) in
       let tm = let uu___3 = aux n in tc uu___3 in
       let hc = FStarC_Syntax_Hash.ext_hash_term tm in
       let uu___3 = FStarC_Compiler_Util.string_of_int n in
       let uu___4 = FStarC_Hash.string_of_hash_code hc in
       FStarC_Compiler_Util.print2 "Hash of unary %s is %s\n" uu___3 uu___4 in
     let rec aux n =
       if n = Prims.int_zero
       then ()
       else (test_one_hash n; aux (n - Prims.int_one)) in
     aux (Prims.of_int (100)); FStarC_Options.init ())
let (parse_incremental_decls : unit -> unit) =
  fun uu___ ->
    let source0 =
      "module Demo\nlet f x = match x with | Some x -> true | None -> false\nlet test y = if Some? y then f y else true\n```pulse\nfn f() {}\n```\n```pulse\nfn g() {}\n```\nlet something = more\nlet >< junk" in
    let source1 =
      "module Demo\nlet f x = match x with | Some x -> true | None -> false\nlet test y = if Some? y then f y else true\n```pulse\nfn f() {}\n```\n\n```pulse\nfn g() {}\n```\nlet something = more\nlet >< junk" in
    let input0 =
      FStarC_Parser_ParseIt.Incremental
        {
          FStarC_Parser_ParseIt.frag_fname = "Demo.fst";
          FStarC_Parser_ParseIt.frag_text = source0;
          FStarC_Parser_ParseIt.frag_line = Prims.int_one;
          FStarC_Parser_ParseIt.frag_col = Prims.int_zero
        } in
    let input1 =
      FStarC_Parser_ParseIt.Incremental
        {
          FStarC_Parser_ParseIt.frag_fname = "Demo.fst";
          FStarC_Parser_ParseIt.frag_text = source1;
          FStarC_Parser_ParseIt.frag_line = Prims.int_one;
          FStarC_Parser_ParseIt.frag_col = Prims.int_zero
        } in
    let uu___1 =
      let uu___2 =
        FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None input0 in
      let uu___3 =
        FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None input1 in
      (uu___2, uu___3) in
    match uu___1 with
    | (FStarC_Parser_ParseIt.IncrementalFragment
       (decls0, uu___2, parse_err0),
       FStarC_Parser_ParseIt.IncrementalFragment
       (decls1, uu___3, parse_err1)) ->
        let check_range r l c =
          let p = FStarC_Compiler_Range_Ops.start_of_range r in
          let uu___4 =
            (let uu___5 = FStarC_Compiler_Range_Ops.line_of_pos p in
             uu___5 = l) &&
              (let uu___5 = FStarC_Compiler_Range_Ops.col_of_pos p in
               uu___5 = c) in
          if uu___4
          then ()
          else
            (let uu___6 =
               let uu___7 = FStarC_Compiler_Util.string_of_int l in
               let uu___8 = FStarC_Compiler_Util.string_of_int c in
               let uu___9 =
                 let uu___10 = FStarC_Compiler_Range_Ops.line_of_pos p in
                 FStarC_Compiler_Util.string_of_int uu___10 in
               let uu___10 =
                 let uu___11 = FStarC_Compiler_Range_Ops.col_of_pos p in
                 FStarC_Compiler_Util.string_of_int uu___11 in
               FStarC_Compiler_Util.format4
                 "Incremental parsing failed: Expected syntax error at (%s, %s), got error at (%s, %s)"
                 uu___7 uu___8 uu___9 uu___10 in
             failwith uu___6) in
        ((match (parse_err0, parse_err1) with
          | (FStar_Pervasives_Native.None, uu___5) ->
              failwith
                "Incremental parsing failed: Expected syntax error at (8, 6), got no error"
          | (uu___5, FStar_Pervasives_Native.None) ->
              failwith
                "Incremental parsing failed: Expected syntax error at (9, 6), got no error"
          | (FStar_Pervasives_Native.Some (uu___5, uu___6, rng0),
             FStar_Pervasives_Native.Some (uu___7, uu___8, rng1)) ->
              (check_range rng0 (Prims.of_int (11)) (Prims.of_int (6));
               check_range rng1 (Prims.of_int (12)) (Prims.of_int (6))));
         (match (decls0, decls1) with
          | (d0::d1::d2::d3::d4::d5::[], e0::e1::e2::e3::e4::e5::[]) ->
              let uu___5 =
                FStarC_Compiler_List.forall2
                  (fun uu___6 ->
                     fun uu___7 ->
                       match (uu___6, uu___7) with
                       | ((x, uu___8), (y, uu___9)) ->
                           FStarC_Parser_AST_Util.eq_decl x y) decls0 decls1 in
              if uu___5
              then ()
              else
                failwith
                  "Incremental parsing failed; unexpected change in a decl"
          | uu___5 ->
              let uu___6 =
                let uu___7 =
                  FStarC_Compiler_Util.string_of_int
                    (FStarC_Compiler_List.length decls0) in
                let uu___8 =
                  FStarC_Compiler_Util.string_of_int
                    (FStarC_Compiler_List.length decls1) in
                FStarC_Compiler_Util.format2
                  "Incremental parsing failed; expected 6 decls got %s and %s\n"
                  uu___7 uu___8 in
              failwith uu___6))
    | (FStarC_Parser_ParseIt.ParseError (code, message, range), uu___2) ->
        let msg =
          let uu___3 = FStarC_Compiler_Range_Ops.string_of_range range in
          let uu___4 = FStarC_Errors_Msg.rendermsg message in
          FStarC_Compiler_Util.format2
            "Incremental parsing failed: Syntax error @ %s: %s" uu___3 uu___4 in
        failwith msg
    | (uu___2, FStarC_Parser_ParseIt.ParseError (code, message, range)) ->
        let msg =
          let uu___3 = FStarC_Compiler_Range_Ops.string_of_range range in
          let uu___4 = FStarC_Errors_Msg.rendermsg message in
          FStarC_Compiler_Util.format2
            "Incremental parsing failed: Syntax error @ %s: %s" uu___3 uu___4 in
        failwith msg
    | uu___2 -> failwith "Incremental parsing failed: Unexpected output"
let (parse_incremental_decls_use_lang : unit -> unit) =
  fun uu___ ->
    let source0 =
      "module Demo\nlet x = 0\n#lang-somelang\nval f : t\nlet g x = f x\n#restart-solver" in
    FStarC_Parser_AST_Util.register_extension_lang_parser "somelang"
      FStarC_Parser_ParseIt.parse_fstar_incrementally;
    (let input0 =
       FStarC_Parser_ParseIt.Incremental
         {
           FStarC_Parser_ParseIt.frag_fname = "Demo.fst";
           FStarC_Parser_ParseIt.frag_text = source0;
           FStarC_Parser_ParseIt.frag_line = Prims.int_one;
           FStarC_Parser_ParseIt.frag_col = Prims.int_zero
         } in
     let uu___2 =
       FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None input0 in
     match uu___2 with
     | FStarC_Parser_ParseIt.IncrementalFragment (decls0, uu___3, parse_err0)
         ->
         ((match parse_err0 with
           | FStar_Pervasives_Native.None -> ()
           | FStar_Pervasives_Native.Some uu___5 ->
               failwith "Incremental parsing failed: ...");
          (let ds =
             FStarC_Compiler_List.map FStar_Pervasives_Native.fst decls0 in
           match ds with
           | { FStarC_Parser_AST.d = FStarC_Parser_AST.TopLevelModule uu___5;
               FStarC_Parser_AST.drange = uu___6;
               FStarC_Parser_AST.quals = uu___7;
               FStarC_Parser_AST.attrs = uu___8;
               FStarC_Parser_AST.interleaved = uu___9;_}::{
                                                            FStarC_Parser_AST.d
                                                              =
                                                              FStarC_Parser_AST.TopLevelLet
                                                              uu___10;
                                                            FStarC_Parser_AST.drange
                                                              = uu___11;
                                                            FStarC_Parser_AST.quals
                                                              = uu___12;
                                                            FStarC_Parser_AST.attrs
                                                              = uu___13;
                                                            FStarC_Parser_AST.interleaved
                                                              = uu___14;_}::
               {
                 FStarC_Parser_AST.d = FStarC_Parser_AST.UseLangDecls uu___15;
                 FStarC_Parser_AST.drange = uu___16;
                 FStarC_Parser_AST.quals = uu___17;
                 FStarC_Parser_AST.attrs = uu___18;
                 FStarC_Parser_AST.interleaved = uu___19;_}::{
                                                               FStarC_Parser_AST.d
                                                                 =
                                                                 FStarC_Parser_AST.Val
                                                                 uu___20;
                                                               FStarC_Parser_AST.drange
                                                                 = uu___21;
                                                               FStarC_Parser_AST.quals
                                                                 = uu___22;
                                                               FStarC_Parser_AST.attrs
                                                                 = uu___23;
                                                               FStarC_Parser_AST.interleaved
                                                                 = uu___24;_}::
               { FStarC_Parser_AST.d = FStarC_Parser_AST.TopLevelLet uu___25;
                 FStarC_Parser_AST.drange = uu___26;
                 FStarC_Parser_AST.quals = uu___27;
                 FStarC_Parser_AST.attrs = uu___28;
                 FStarC_Parser_AST.interleaved = uu___29;_}::{
                                                               FStarC_Parser_AST.d
                                                                 =
                                                                 FStarC_Parser_AST.Pragma
                                                                 uu___30;
                                                               FStarC_Parser_AST.drange
                                                                 = uu___31;
                                                               FStarC_Parser_AST.quals
                                                                 = uu___32;
                                                               FStarC_Parser_AST.attrs
                                                                 = uu___33;
                                                               FStarC_Parser_AST.interleaved
                                                                 = uu___34;_}::[]
               -> ()
           | uu___5 ->
               let uu___6 =
                 let uu___7 =
                   FStarC_Class_Show.show
                     (FStarC_Class_Show.show_list
                        FStarC_Parser_AST.showable_decl) ds in
                 Prims.strcat
                   "Incremental parsing failed; unexpected decls: " uu___7 in
               failwith uu___6))
     | FStarC_Parser_ParseIt.ParseError (code, message, range) ->
         let msg =
           let uu___3 = FStarC_Compiler_Range_Ops.string_of_range range in
           let uu___4 = FStarC_Errors_Msg.rendermsg message in
           FStarC_Compiler_Util.format2
             "Incremental parsing failed: Syntax error @ %s: %s" uu___3
             uu___4 in
         failwith msg
     | uu___3 -> failwith "Incremental parsing failed: Unexpected output")