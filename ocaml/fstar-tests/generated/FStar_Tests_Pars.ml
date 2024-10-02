open Prims
let (test_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Test"] FStar_Compiler_Range_Type.dummyRange
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
        FStar_Parser_ParseIt.parse FStar_Pervasives_Native.None
          (FStar_Parser_ParseIt.Filename mod_name) in
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
                     FStar_Compiler_Range_Type.dummyRange in
                 FStar_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu___4 FStar_Syntax_DsEnv.default_mii in
               (match uu___3 with | (env'1, uu___4) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (err, msg, r) ->
          FStar_Compiler_Effect.raise (FStar_Errors.Error (err, msg, r, []))
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Pervasives.Inr uu___1, uu___2) ->
          let msg =
            FStar_Compiler_Util.format1 "%s: expected a module\n" mod_name in
          FStar_Errors.raise_error0 FStar_Errors_Codes.Fatal_ModuleExpected
            () (Obj.magic FStar_Errors_Msg.is_error_message_string)
            (Obj.magic msg)
      | FStar_Parser_ParseIt.Term uu___1 ->
          FStar_Compiler_Effect.failwith
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
             FStar_TypeChecker_Env.lax_universes =
               (env.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (env.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (env.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.flychecking =
               (env.FStar_TypeChecker_Env.flychecking);
             FStar_TypeChecker_Env.uvar_subtyping =
               (env.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.intactics =
               (env.FStar_TypeChecker_Env.intactics);
             FStar_TypeChecker_Env.nocoerce =
               (env.FStar_TypeChecker_Env.nocoerce);
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
               (env.FStar_TypeChecker_Env.core_check);
             FStar_TypeChecker_Env.missing_decl =
               (env.FStar_TypeChecker_Env.missing_decl)
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
                  FStar_TypeChecker_Env.lax_universes =
                    (env2.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (env2.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (env2.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.flychecking =
                    (env2.FStar_TypeChecker_Env.flychecking);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (env2.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.intactics =
                    (env2.FStar_TypeChecker_Env.intactics);
                  FStar_TypeChecker_Env.nocoerce =
                    (env2.FStar_TypeChecker_Env.nocoerce);
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
                    (env2.FStar_TypeChecker_Env.core_check);
                  FStar_TypeChecker_Env.missing_decl =
                    (env2.FStar_TypeChecker_Env.missing_decl)
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
        FStar_Compiler_Effect.failwith
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
               FStar_Parser_ParseIt.parse FStar_Pervasives_Native.None
                 (FStar_Parser_ParseIt.Fragment (frag_of_text s)) in
             (match uu___1 with
              | FStar_Parser_ParseIt.Term t ->
                  FStar_ToSyntax_ToSyntax.desugar_term
                    tcenv.FStar_TypeChecker_Env.dsenv t
              | FStar_Parser_ParseIt.ParseError (e, msg, r) ->
                  FStar_Errors.raise_error
                    FStar_Class_HasRange.hasRange_range r e ()
                    (Obj.magic FStar_Errors_Msg.is_error_message_list_doc)
                    (Obj.magic msg)
              | FStar_Parser_ParseIt.ASTFragment uu___2 ->
                  FStar_Compiler_Effect.failwith
                    "Impossible: parsing a Fragment always results in a Term"))
        ()
    with
    | FStar_Errors.Error (err, msg, r, _ctx) when
        let uu___1 = FStar_Options.trace_error () in Prims.op_Negation uu___1
        ->
        (if r = FStar_Compiler_Range_Type.dummyRange
         then
           (let uu___2 = FStar_Errors_Msg.rendermsg msg in
            FStar_Compiler_Util.print_string uu___2)
         else
           (let uu___3 = FStar_Compiler_Range_Ops.string_of_range r in
            let uu___4 = FStar_Errors_Msg.rendermsg msg in
            FStar_Compiler_Util.print2 "%s: %s\n" uu___3 uu___4);
         FStar_Compiler_Effect.exit Prims.int_one)
    | e when
        let uu___1 = FStar_Options.trace_error () in Prims.op_Negation uu___1
        -> FStar_Compiler_Effect.raise e
let (tc' :
  Prims.string -> (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.env)) =
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
        FStar_TypeChecker_Env.lax_universes =
          (tcenv.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = true;
        FStar_TypeChecker_Env.failhard =
          (tcenv.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.flychecking =
          (tcenv.FStar_TypeChecker_Env.flychecking);
        FStar_TypeChecker_Env.uvar_subtyping =
          (tcenv.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.intactics =
          (tcenv.FStar_TypeChecker_Env.intactics);
        FStar_TypeChecker_Env.nocoerce =
          (tcenv.FStar_TypeChecker_Env.nocoerce);
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
          (tcenv.FStar_TypeChecker_Env.core_check);
        FStar_TypeChecker_Env.missing_decl =
          (tcenv.FStar_TypeChecker_Env.missing_decl)
      } in
    let uu___ = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu___ with
    | (tm1, uu___1, g) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g;
         (let tm2 = FStar_Syntax_Compress.deep_compress false false tm1 in
          (tm2, tcenv1)))
let (tc : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s -> let uu___ = tc' s in match uu___ with | (tm, uu___1) -> tm
let (tc_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
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
        FStar_TypeChecker_Env.lax_universes =
          (tcenv.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (tcenv.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (tcenv.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.flychecking =
          (tcenv.FStar_TypeChecker_Env.flychecking);
        FStar_TypeChecker_Env.uvar_subtyping =
          (tcenv.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.intactics =
          (tcenv.FStar_TypeChecker_Env.intactics);
        FStar_TypeChecker_Env.nocoerce =
          (tcenv.FStar_TypeChecker_Env.nocoerce);
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
          (tcenv.FStar_TypeChecker_Env.core_check);
        FStar_TypeChecker_Env.missing_decl =
          (tcenv.FStar_TypeChecker_Env.missing_decl)
      } in
    let uu___ = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu___ with
    | (tm1, uu___1, g) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g;
         (let tm2 = FStar_Syntax_Compress.deep_compress false false tm1 in
          tm2))
let (pars_and_tc_fragment : Prims.string -> unit) =
  fun s ->
    FStar_Options.set_option "trace_error" (FStar_Options.Bool true);
    (let report uu___1 = let uu___2 = FStar_Errors.report_all () in () in
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
                          FStar_Universal.tc_one_fragment uu___4 tcenv
                            (FStar_Pervasives.Inl (frag, [])) in
                        (match uu___3 with
                         | (test_mod', tcenv', uu___4) ->
                             (FStar_Compiler_Effect.op_Colon_Equals
                                test_mod_ref test_mod';
                              FStar_Compiler_Effect.op_Colon_Equals tcenv_ref
                                (FStar_Pervasives_Native.Some tcenv');
                              (let n = FStar_Errors.get_err_count () in
                               if n <> Prims.int_zero
                               then
                                 (report ();
                                  (let uu___8 =
                                     let uu___9 =
                                       FStar_Compiler_Util.string_of_int n in
                                     FStar_Compiler_Util.format1
                                       "%s errors were reported" uu___9 in
                                   FStar_Errors.raise_error0
                                     FStar_Errors_Codes.Fatal_ErrorsReported
                                     ()
                                     (Obj.magic
                                        FStar_Errors_Msg.is_error_message_string)
                                     (Obj.magic uu___8)))
                               else ())))) ()
               with
               | uu___2 ->
                   (report ();
                    FStar_Errors.raise_error0
                      FStar_Errors_Codes.Fatal_TcOneFragmentFailed ()
                      (Obj.magic FStar_Errors_Msg.is_error_message_string)
                      (Obj.magic (Prims.strcat "tc_one_fragment failed: " s)))))
         ()
     with
     | uu___1 ->
         ((fun uu___1 ->
             if
               let uu___2 = FStar_Options.trace_error () in
               Prims.op_Negation uu___2
             then Obj.magic (Obj.repr (FStar_Compiler_Effect.raise uu___1))
             else Obj.magic (Obj.repr (failwith "unreachable")))) uu___1)
let (test_hashes : unit -> unit) =
  fun uu___ ->
    (let uu___2 = FStar_Main.process_args () in ());
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
       let hc = FStar_Syntax_Hash.ext_hash_term tm in
       let uu___3 = FStar_Compiler_Util.string_of_int n in
       let uu___4 = FStar_Hash.string_of_hash_code hc in
       FStar_Compiler_Util.print2 "Hash of unary %s is %s\n" uu___3 uu___4 in
     let rec aux n =
       if n = Prims.int_zero
       then ()
       else (test_one_hash n; aux (n - Prims.int_one)) in
     aux (Prims.of_int (100)); FStar_Options.init ())
let (parse_incremental_decls : unit -> unit) =
  fun uu___ ->
    let source0 =
      "module Demo\nlet f x = match x with | Some x -> true | None -> false\nlet test y = if Some? y then f y else true\n```pulse\nfn f() {}\n```\n```pulse\nfn g() {}\n```\nlet something = more\nlet >< junk" in
    let source1 =
      "module Demo\nlet f x = match x with | Some x -> true | None -> false\nlet test y = if Some? y then f y else true\n```pulse\nfn f() {}\n```\n\n```pulse\nfn g() {}\n```\nlet something = more\nlet >< junk" in
    let input0 =
      FStar_Parser_ParseIt.Incremental
        {
          FStar_Parser_ParseIt.frag_fname = "Demo.fst";
          FStar_Parser_ParseIt.frag_text = source0;
          FStar_Parser_ParseIt.frag_line = Prims.int_one;
          FStar_Parser_ParseIt.frag_col = Prims.int_zero
        } in
    let input1 =
      FStar_Parser_ParseIt.Incremental
        {
          FStar_Parser_ParseIt.frag_fname = "Demo.fst";
          FStar_Parser_ParseIt.frag_text = source1;
          FStar_Parser_ParseIt.frag_line = Prims.int_one;
          FStar_Parser_ParseIt.frag_col = Prims.int_zero
        } in
    let uu___1 =
      let uu___2 =
        FStar_Parser_ParseIt.parse FStar_Pervasives_Native.None input0 in
      let uu___3 =
        FStar_Parser_ParseIt.parse FStar_Pervasives_Native.None input1 in
      (uu___2, uu___3) in
    match uu___1 with
    | (FStar_Parser_ParseIt.IncrementalFragment (decls0, uu___2, parse_err0),
       FStar_Parser_ParseIt.IncrementalFragment (decls1, uu___3, parse_err1))
        ->
        let check_range r l c =
          let p = FStar_Compiler_Range_Ops.start_of_range r in
          let uu___4 =
            (let uu___5 = FStar_Compiler_Range_Ops.line_of_pos p in
             uu___5 = l) &&
              (let uu___5 = FStar_Compiler_Range_Ops.col_of_pos p in
               uu___5 = c) in
          if uu___4
          then ()
          else
            (let uu___6 =
               let uu___7 = FStar_Compiler_Util.string_of_int l in
               let uu___8 = FStar_Compiler_Util.string_of_int c in
               let uu___9 =
                 let uu___10 = FStar_Compiler_Range_Ops.line_of_pos p in
                 FStar_Compiler_Util.string_of_int uu___10 in
               let uu___10 =
                 let uu___11 = FStar_Compiler_Range_Ops.col_of_pos p in
                 FStar_Compiler_Util.string_of_int uu___11 in
               FStar_Compiler_Util.format4
                 "Incremental parsing failed: Expected syntax error at (%s, %s), got error at (%s, %s)"
                 uu___7 uu___8 uu___9 uu___10 in
             FStar_Compiler_Effect.failwith uu___6) in
        ((match (parse_err0, parse_err1) with
          | (FStar_Pervasives_Native.None, uu___5) ->
              FStar_Compiler_Effect.failwith
                "Incremental parsing failed: Expected syntax error at (8, 6), got no error"
          | (uu___5, FStar_Pervasives_Native.None) ->
              FStar_Compiler_Effect.failwith
                "Incremental parsing failed: Expected syntax error at (9, 6), got no error"
          | (FStar_Pervasives_Native.Some (uu___5, uu___6, rng0),
             FStar_Pervasives_Native.Some (uu___7, uu___8, rng1)) ->
              (check_range rng0 (Prims.of_int (11)) (Prims.of_int (6));
               check_range rng1 (Prims.of_int (12)) (Prims.of_int (6))));
         (match (decls0, decls1) with
          | (d0::d1::d2::d3::d4::d5::[], e0::e1::e2::e3::e4::e5::[]) ->
              let uu___5 =
                FStar_Compiler_List.forall2
                  (fun uu___6 ->
                     fun uu___7 ->
                       match (uu___6, uu___7) with
                       | ((x, uu___8), (y, uu___9)) ->
                           FStar_Parser_AST_Util.eq_decl x y) decls0 decls1 in
              if uu___5
              then ()
              else
                FStar_Compiler_Effect.failwith
                  "Incremental parsing failed; unexpected change in a decl"
          | uu___5 ->
              let uu___6 =
                let uu___7 =
                  FStar_Compiler_Util.string_of_int
                    (FStar_Compiler_List.length decls0) in
                let uu___8 =
                  FStar_Compiler_Util.string_of_int
                    (FStar_Compiler_List.length decls1) in
                FStar_Compiler_Util.format2
                  "Incremental parsing failed; expected 6 decls got %s and %s\n"
                  uu___7 uu___8 in
              FStar_Compiler_Effect.failwith uu___6))
    | (FStar_Parser_ParseIt.ParseError (code, message, range), uu___2) ->
        let msg =
          let uu___3 = FStar_Compiler_Range_Ops.string_of_range range in
          let uu___4 = FStar_Errors_Msg.rendermsg message in
          FStar_Compiler_Util.format2
            "Incremental parsing failed: Syntax error @ %s: %s" uu___3 uu___4 in
        FStar_Compiler_Effect.failwith msg
    | (uu___2, FStar_Parser_ParseIt.ParseError (code, message, range)) ->
        let msg =
          let uu___3 = FStar_Compiler_Range_Ops.string_of_range range in
          let uu___4 = FStar_Errors_Msg.rendermsg message in
          FStar_Compiler_Util.format2
            "Incremental parsing failed: Syntax error @ %s: %s" uu___3 uu___4 in
        FStar_Compiler_Effect.failwith msg
    | uu___2 ->
        FStar_Compiler_Effect.failwith
          "Incremental parsing failed: Unexpected output"
let (parse_incremental_decls_use_lang : unit -> unit) =
  fun uu___ ->
    let source0 =
      "module Demo\nlet x = 0\n#lang-somelang\nval f : t\nlet g x = f x\n#restart-solver" in
    FStar_Parser_AST_Util.register_extension_lang_parser "somelang"
      FStar_Parser_ParseIt.parse_fstar_incrementally;
    (let input0 =
       FStar_Parser_ParseIt.Incremental
         {
           FStar_Parser_ParseIt.frag_fname = "Demo.fst";
           FStar_Parser_ParseIt.frag_text = source0;
           FStar_Parser_ParseIt.frag_line = Prims.int_one;
           FStar_Parser_ParseIt.frag_col = Prims.int_zero
         } in
     let uu___2 =
       FStar_Parser_ParseIt.parse FStar_Pervasives_Native.None input0 in
     match uu___2 with
     | FStar_Parser_ParseIt.IncrementalFragment (decls0, uu___3, parse_err0)
         ->
         ((match parse_err0 with
           | FStar_Pervasives_Native.None -> ()
           | FStar_Pervasives_Native.Some uu___5 ->
               FStar_Compiler_Effect.failwith
                 "Incremental parsing failed: ...");
          (let ds =
             FStar_Compiler_List.map FStar_Pervasives_Native.fst decls0 in
           match ds with
           | { FStar_Parser_AST.d = FStar_Parser_AST.TopLevelModule uu___5;
               FStar_Parser_AST.drange = uu___6;
               FStar_Parser_AST.quals = uu___7;
               FStar_Parser_AST.attrs = uu___8;
               FStar_Parser_AST.interleaved = uu___9;_}::{
                                                           FStar_Parser_AST.d
                                                             =
                                                             FStar_Parser_AST.TopLevelLet
                                                             uu___10;
                                                           FStar_Parser_AST.drange
                                                             = uu___11;
                                                           FStar_Parser_AST.quals
                                                             = uu___12;
                                                           FStar_Parser_AST.attrs
                                                             = uu___13;
                                                           FStar_Parser_AST.interleaved
                                                             = uu___14;_}::
               { FStar_Parser_AST.d = FStar_Parser_AST.UseLangDecls uu___15;
                 FStar_Parser_AST.drange = uu___16;
                 FStar_Parser_AST.quals = uu___17;
                 FStar_Parser_AST.attrs = uu___18;
                 FStar_Parser_AST.interleaved = uu___19;_}::{
                                                              FStar_Parser_AST.d
                                                                =
                                                                FStar_Parser_AST.Val
                                                                uu___20;
                                                              FStar_Parser_AST.drange
                                                                = uu___21;
                                                              FStar_Parser_AST.quals
                                                                = uu___22;
                                                              FStar_Parser_AST.attrs
                                                                = uu___23;
                                                              FStar_Parser_AST.interleaved
                                                                = uu___24;_}::
               { FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet uu___25;
                 FStar_Parser_AST.drange = uu___26;
                 FStar_Parser_AST.quals = uu___27;
                 FStar_Parser_AST.attrs = uu___28;
                 FStar_Parser_AST.interleaved = uu___29;_}::{
                                                              FStar_Parser_AST.d
                                                                =
                                                                FStar_Parser_AST.Pragma
                                                                uu___30;
                                                              FStar_Parser_AST.drange
                                                                = uu___31;
                                                              FStar_Parser_AST.quals
                                                                = uu___32;
                                                              FStar_Parser_AST.attrs
                                                                = uu___33;
                                                              FStar_Parser_AST.interleaved
                                                                = uu___34;_}::[]
               -> ()
           | uu___5 ->
               let uu___6 =
                 let uu___7 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.show_list
                        FStar_Parser_AST.showable_decl) ds in
                 Prims.strcat
                   "Incremental parsing failed; unexpected decls: " uu___7 in
               FStar_Compiler_Effect.failwith uu___6))
     | FStar_Parser_ParseIt.ParseError (code, message, range) ->
         let msg =
           let uu___3 = FStar_Compiler_Range_Ops.string_of_range range in
           let uu___4 = FStar_Errors_Msg.rendermsg message in
           FStar_Compiler_Util.format2
             "Incremental parsing failed: Syntax error @ %s: %s" uu___3
             uu___4 in
         FStar_Compiler_Effect.failwith msg
     | uu___3 ->
         FStar_Compiler_Effect.failwith
           "Incremental parsing failed: Unexpected output")