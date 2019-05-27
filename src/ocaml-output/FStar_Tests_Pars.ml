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
         FStar_Syntax_Syntax.exports = [];
         FStar_Syntax_Syntax.is_interface = false
       })
let (parse_mod :
  Prims.string ->
    FStar_Syntax_DsEnv.env ->
      (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.modul))
  =
  fun mod_name1 ->
    fun dsenv1 ->
      let uu____35 =
        FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename mod_name1) in
      match uu____35 with
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl m, uu____41) ->
          let uu____58 =
            let uu____63 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul m in
            uu____63 dsenv1 in
          (match uu____58 with
           | (m1, env') ->
               let uu____74 =
                 let uu____80 =
                   FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange in
                 FStar_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu____80 FStar_Syntax_DsEnv.default_mii in
               (match uu____74 with | (env'1, uu____91) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (err, msg, r) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, r))
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Util.Inr uu____104, uu____105) ->
          let msg = FStar_Util.format1 "%s: expected a module\n" mod_name1 in
          FStar_Errors.raise_error (FStar_Errors.Fatal_ModuleExpected, msg)
            FStar_Range.dummyRange
      | FStar_Parser_ParseIt.Term uu____132 ->
          failwith
            "Impossible: parsing a Filename always results in an ASTFragment"
let (add_mods :
  Prims.string Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_Syntax_DsEnv.env * FStar_TypeChecker_Env.env))
  =
  fun mod_names ->
    fun dsenv1 ->
      fun env ->
        FStar_List.fold_left
          (fun uu____179 ->
             fun mod_name1 ->
               match uu____179 with
               | (dsenv2, env1) ->
                   let uu____192 = parse_mod mod_name1 dsenv2 in
                   (match uu____192 with
                    | (dsenv3, string_mod) ->
                        let uu____203 =
                          FStar_TypeChecker_Tc.check_module env1 string_mod
                            false in
                        (match uu____203 with
                         | (_mod, env2) -> (dsenv3, env2)))) (dsenv1, env)
          mod_names
let (init_once : unit -> unit) =
  fun uu____220 ->
    let solver1 = FStar_SMTEncoding_Solver.dummy in
    let env =
      FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps
        FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid
        FStar_TypeChecker_NBE.normalize_for_unit_test in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let uu____224 =
       let uu____229 = FStar_Options.prims () in
       let uu____231 =
         FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps in
       parse_mod uu____229 uu____231 in
     match uu____224 with
     | (dsenv1, prims_mod) ->
         let env1 =
           let uu___46_235 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___46_235.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___46_235.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___46_235.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___46_235.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___46_235.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___46_235.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___46_235.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___46_235.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___46_235.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___46_235.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___46_235.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___46_235.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___46_235.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___46_235.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___46_235.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___46_235.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___46_235.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___46_235.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___46_235.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___46_235.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___46_235.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___46_235.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___46_235.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___46_235.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___46_235.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___46_235.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___46_235.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___46_235.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___46_235.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___46_235.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___46_235.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___46_235.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___46_235.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___46_235.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___46_235.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___46_235.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___46_235.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___46_235.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___46_235.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___46_235.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___46_235.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = dsenv1;
             FStar_TypeChecker_Env.nbe =
               (uu___46_235.FStar_TypeChecker_Env.nbe)
           } in
         let uu____236 =
           FStar_TypeChecker_Tc.check_module env1 prims_mod false in
         (match uu____236 with
          | (_prims_mod, env2) ->
              let env3 =
                let uu___52_245 = env2 in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___52_245.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___52_245.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___52_245.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___52_245.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___52_245.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___52_245.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___52_245.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___52_245.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___52_245.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___52_245.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___52_245.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___52_245.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___52_245.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___52_245.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___52_245.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___52_245.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___52_245.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___52_245.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___52_245.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___52_245.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___52_245.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___52_245.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___52_245.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___52_245.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___52_245.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___52_245.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___52_245.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___52_245.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___52_245.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___52_245.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___52_245.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___52_245.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___52_245.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___52_245.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___52_245.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___52_245.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___52_245.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___52_245.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___52_245.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___52_245.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___52_245.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv = dsenv1;
                  FStar_TypeChecker_Env.nbe =
                    (uu___52_245.FStar_TypeChecker_Env.nbe)
                } in
              let env4 =
                FStar_TypeChecker_Env.set_current_module env3 test_lid in
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env4)))
let (uu___56 : unit) = FStar_Main.setup_hooks (); init_once ()
let (init : unit -> FStar_TypeChecker_Env.env) =
  fun uu____277 ->
    let uu____278 = FStar_ST.op_Bang tcenv_ref in
    match uu____278 with
    | FStar_Pervasives_Native.Some f -> f
    | uu____305 ->
        failwith
          "Should have already been initialized by the top-level effect"
let (frag_of_text : Prims.string -> FStar_Parser_ParseIt.input_frag) =
  fun s ->
    {
      FStar_Parser_ParseIt.frag_fname = "<input>";
      FStar_Parser_ParseIt.frag_text = s;
      FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
      FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
    }
let (pars : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    try
      (fun uu___65_332 ->
         match () with
         | () ->
             let tcenv = init () in
             let uu____334 =
               let uu____335 =
                 FStar_All.pipe_left
                   (fun _336 -> FStar_Parser_ParseIt.Fragment _336)
                   (frag_of_text s) in
               FStar_Parser_ParseIt.parse uu____335 in
             (match uu____334 with
              | FStar_Parser_ParseIt.Term t ->
                  FStar_ToSyntax_ToSyntax.desugar_term
                    tcenv.FStar_TypeChecker_Env.dsenv t
              | FStar_Parser_ParseIt.ParseError (e, msg, r) ->
                  FStar_Errors.raise_error (e, msg) r
              | FStar_Parser_ParseIt.ASTFragment uu____344 ->
                  failwith
                    "Impossible: parsing a Fragment always results in a Term"))
        ()
    with
    | uu___64_358 ->
        if
          let uu____359 = FStar_Options.trace_error () in
          Prims.op_Negation uu____359
        then Obj.magic (Obj.repr (FStar_Exn.raise uu___64_358))
        else Obj.magic (Obj.repr (failwith "unreachable"))
let (tc' :
  Prims.string ->
    (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t *
      FStar_TypeChecker_Env.env))
  =
  fun s ->
    let tm = pars s in
    let tcenv = init () in
    let tcenv1 =
      let uu___83_378 = tcenv in
      {
        FStar_TypeChecker_Env.solver =
          (uu___83_378.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___83_378.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___83_378.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___83_378.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___83_378.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___83_378.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___83_378.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___83_378.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___83_378.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___83_378.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___83_378.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___83_378.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___83_378.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___83_378.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___83_378.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___83_378.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___83_378.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___83_378.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___83_378.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___83_378.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___83_378.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___83_378.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___83_378.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___83_378.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___83_378.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___83_378.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___83_378.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___83_378.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___83_378.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___83_378.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___83_378.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___83_378.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___83_378.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___83_378.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___83_378.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___83_378.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___83_378.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___83_378.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___83_378.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___83_378.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___83_378.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___83_378.FStar_TypeChecker_Env.nbe)
      } in
    let uu____380 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu____380 with | (tm1, uu____394, g) -> (tm1, g, tcenv1)
let (tc : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    let uu____404 = tc' s in
    match uu____404 with | (tm, uu____412, uu____413) -> tm
let (tc_nbe : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    let uu____422 = tc' s in
    match uu____422 with
    | (tm, g, tcenv) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv g; tm)
let (tc_nbe_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun tm ->
    let tcenv = init () in
    let tcenv1 =
      let uu___103_441 = tcenv in
      {
        FStar_TypeChecker_Env.solver =
          (uu___103_441.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___103_441.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___103_441.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___103_441.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___103_441.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___103_441.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___103_441.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___103_441.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___103_441.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___103_441.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___103_441.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___103_441.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___103_441.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___103_441.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___103_441.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___103_441.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___103_441.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___103_441.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___103_441.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___103_441.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___103_441.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___103_441.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___103_441.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___103_441.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___103_441.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___103_441.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___103_441.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___103_441.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___103_441.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___103_441.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___103_441.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___103_441.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___103_441.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___103_441.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___103_441.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___103_441.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___103_441.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___103_441.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___103_441.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___103_441.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___103_441.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___103_441.FStar_TypeChecker_Env.nbe)
      } in
    let uu____443 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu____443 with
    | (tm1, uu____451, g) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g; tm1)
let (pars_and_tc_fragment : Prims.string -> unit) =
  fun s ->
    FStar_Options.set_option "trace_error" (FStar_Options.Bool true);
    (let report uu____470 =
       let uu____471 = FStar_Errors.report_all () in
       FStar_All.pipe_right uu____471 (fun a1 -> ()) in
     try
       (fun uu___116_479 ->
          match () with
          | () ->
              let tcenv = init () in
              let frag = frag_of_text s in
              (try
                 (fun uu___124_491 ->
                    match () with
                    | () ->
                        let uu____492 =
                          let uu____499 = FStar_ST.op_Bang test_mod_ref in
                          FStar_Universal.tc_one_fragment uu____499 tcenv
                            frag in
                        (match uu____492 with
                         | (test_mod', tcenv') ->
                             (FStar_ST.op_Colon_Equals test_mod_ref test_mod';
                              FStar_ST.op_Colon_Equals tcenv_ref
                                (FStar_Pervasives_Native.Some tcenv');
                              (let n1 = FStar_Errors.get_err_count () in
                               if n1 <> (Prims.parse_int "0")
                               then
                                 (report ();
                                  (let uu____585 =
                                     let uu____591 =
                                       let uu____593 =
                                         FStar_Util.string_of_int n1 in
                                       FStar_Util.format1
                                         "%s errors were reported" uu____593 in
                                     (FStar_Errors.Fatal_ErrorsReported,
                                       uu____591) in
                                   FStar_Errors.raise_err uu____585))
                               else ())))) ()
               with
               | uu___123_601 ->
                   (report ();
                    FStar_Errors.raise_err
                      (FStar_Errors.Fatal_TcOneFragmentFailed,
                        (Prims.op_Hat "tc_one_fragment failed: " s))))) ()
     with
     | uu___115_606 ->
         if
           let uu____607 = FStar_Options.trace_error () in
           Prims.op_Negation uu____607
         then Obj.magic (Obj.repr (FStar_Exn.raise uu___115_606))
         else Obj.magic (Obj.repr (failwith "unreachable")))