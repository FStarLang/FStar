open Prims
let (test_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange
let (tcenv_ref :
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (test_mod_ref :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref
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
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl m, uu___1) ->
          let uu___2 =
            let uu___3 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul m in
            uu___3 dsenv in
          (match uu___2 with
           | (m1, env') ->
               let uu___3 =
                 let uu___4 =
                   FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange in
                 FStar_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu___4 FStar_Syntax_DsEnv.default_mii in
               (match uu___3 with | (env'1, uu___4) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (err, msg, r) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, r, []))
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr uu___1, uu___2) ->
          let msg = FStar_Util.format1 "%s: expected a module\n" mod_name in
          FStar_Errors.raise_error (FStar_Errors.Fatal_ModuleExpected, msg)
            FStar_Range.dummyRange
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
        FStar_List.fold_left
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
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver
        FStar_Parser_Const.prims_lid
        FStar_TypeChecker_NBE.normalize_for_unit_test in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let uu___2 =
       let uu___3 = FStar_Options.prims () in
       let uu___4 = FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps in
       parse_mod uu___3 uu___4 in
     match uu___2 with
     | (dsenv, prims_mod) ->
         let env1 =
           let uu___3 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___3.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___3.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___3.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___3.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___3.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___3.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___3.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___3.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___3.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___3.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___3.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___3.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___3.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___3.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___3.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___3.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___3.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___3.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___3.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___3.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax = (uu___3.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___3.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___3.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___3.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___3.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___3.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___3.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___3.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___3.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___3.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___3.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___3.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___3.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___3.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___3.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___3.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___3.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___3.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___3.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___3.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___3.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___3.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = dsenv;
             FStar_TypeChecker_Env.nbe = (uu___3.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___3.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___3.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___3.FStar_TypeChecker_Env.enable_defer_to_tac)
           } in
         let uu___3 = FStar_TypeChecker_Tc.check_module env1 prims_mod false in
         (match uu___3 with
          | (_prims_mod, env2) ->
              let env3 =
                let uu___4 = env2 in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___4.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___4.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___4.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___4.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___4.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___4.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___4.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___4.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___4.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___4.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___4.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___4.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___4.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___4.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___4.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___4.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___4.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.use_eq_strict =
                    (uu___4.FStar_TypeChecker_Env.use_eq_strict);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___4.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___4.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___4.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___4.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___4.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___4.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___4.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___4.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___4.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___4.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___4.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___4.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___4.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___4.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___4.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___4.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___4.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___4.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.try_solve_implicits_hook =
                    (uu___4.FStar_TypeChecker_Env.try_solve_implicits_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___4.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.mpreprocess =
                    (uu___4.FStar_TypeChecker_Env.mpreprocess);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___4.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___4.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___4.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv = dsenv;
                  FStar_TypeChecker_Env.nbe =
                    (uu___4.FStar_TypeChecker_Env.nbe);
                  FStar_TypeChecker_Env.strict_args_tab =
                    (uu___4.FStar_TypeChecker_Env.strict_args_tab);
                  FStar_TypeChecker_Env.erasable_types_tab =
                    (uu___4.FStar_TypeChecker_Env.erasable_types_tab);
                  FStar_TypeChecker_Env.enable_defer_to_tac =
                    (uu___4.FStar_TypeChecker_Env.enable_defer_to_tac)
                } in
              let env4 =
                FStar_TypeChecker_Env.set_current_module env3 test_lid in
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env4)))
let (uu___56 : unit) = FStar_Main.setup_hooks (); init_once ()
let (init : unit -> FStar_TypeChecker_Env.env) =
  fun uu___ ->
    let uu___1 = FStar_ST.op_Bang tcenv_ref in
    match uu___1 with
    | FStar_Pervasives_Native.Some f -> f
    | uu___2 ->
        failwith
          "Should have already been initialized by the top-level effect"
let (frag_of_text : Prims.string -> FStar_Parser_ParseIt.input_frag) =
  fun s ->
    {
      FStar_Parser_ParseIt.frag_fname = "<input>";
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
                 FStar_All.pipe_left
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
    | uu___ ->
        if
          let uu___1 = FStar_Options.trace_error () in
          Prims.op_Negation uu___1
        then Obj.magic (Obj.repr (FStar_Exn.raise uu___))
        else Obj.magic (Obj.repr (failwith "unreachable"))
let (tc' :
  Prims.string ->
    (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t *
      FStar_TypeChecker_Env.env))
  =
  fun s ->
    let tm = pars s in
    let tcenv = init () in
    let tcenv1 =
      let uu___ = tcenv in
      {
        FStar_TypeChecker_Env.solver = (uu___.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (uu___.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (uu___.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (uu___.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (uu___.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (uu___.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (uu___.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (uu___.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq = (uu___.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (uu___.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (uu___.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (uu___.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (uu___.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of = (uu___.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice = (uu___.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (uu___.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___.FStar_TypeChecker_Env.enable_defer_to_tac)
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
      let uu___ = tcenv in
      {
        FStar_TypeChecker_Env.solver = (uu___.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (uu___.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (uu___.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules = (uu___.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab = (uu___.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab = (uu___.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects = (uu___.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs = (uu___.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq = (uu___.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (uu___.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (uu___.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (uu___.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (uu___.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of = (uu___.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice = (uu___.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = (uu___.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___.FStar_TypeChecker_Env.enable_defer_to_tac)
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
       FStar_All.pipe_right uu___2 (fun uu___3 -> ()) in
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
                          let uu___4 = FStar_ST.op_Bang test_mod_ref in
                          FStar_Universal.tc_one_fragment uu___4 tcenv frag in
                        (match uu___3 with
                         | (test_mod', tcenv') ->
                             (FStar_ST.op_Colon_Equals test_mod_ref test_mod';
                              FStar_ST.op_Colon_Equals tcenv_ref
                                (FStar_Pervasives_Native.Some tcenv');
                              (let n = FStar_Errors.get_err_count () in
                               if n <> Prims.int_zero
                               then
                                 (report ();
                                  (let uu___7 =
                                     let uu___8 =
                                       let uu___9 =
                                         FStar_Util.string_of_int n in
                                       FStar_Util.format1
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
         then Obj.magic (Obj.repr (FStar_Exn.raise uu___1))
         else Obj.magic (Obj.repr (failwith "unreachable")))