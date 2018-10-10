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
      (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.modul)
        FStar_Pervasives_Native.tuple2)
  =
  fun mod_name1  ->
    fun dsenv1  ->
      let uu____58 =
        FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename mod_name1)
         in
      match uu____58 with
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl m,uu____64) ->
          let uu____81 =
            let uu____86 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul m  in
            uu____86 dsenv1  in
          (match uu____81 with
           | (m1,env') ->
               let uu____99 =
                 let uu____105 =
                   FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange
                    in
                 FStar_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu____105 FStar_Syntax_DsEnv.default_mii
                  in
               (match uu____99 with | (env'1,uu____116) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (err,msg,r) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, r))
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr uu____129,uu____130)
          ->
          let msg = FStar_Util.format1 "%s: expected a module\n" mod_name1
             in
          FStar_Errors.raise_error (FStar_Errors.Fatal_ModuleExpected, msg)
            FStar_Range.dummyRange
      | FStar_Parser_ParseIt.Term uu____157 ->
          failwith
            "Impossible: parsing a Filename always results in an ASTFragment"
  
let (add_mods :
  Prims.string Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_Syntax_DsEnv.env,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun mod_names  ->
    fun dsenv1  ->
      fun env  ->
        FStar_List.fold_left
          (fun uu____205  ->
             fun mod_name1  ->
               match uu____205 with
               | (dsenv2,env1) ->
                   let uu____218 = parse_mod mod_name1 dsenv2  in
                   (match uu____218 with
                    | (dsenv3,string_mod) ->
                        let uu____229 =
                          FStar_TypeChecker_Tc.check_module env1 string_mod
                            false
                           in
                        (match uu____229 with
                         | (_mod,uu____244,env2) -> (dsenv3, env2))))
          (dsenv1, env) mod_names
  
let (init_once : unit -> unit) =
  fun uu____255  ->
    let solver1 = FStar_SMTEncoding_Solver.dummy  in
    let env =
      FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps
        FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid
        FStar_TypeChecker_NBE.normalize_for_unit_test
       in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let uu____259 =
       let uu____264 = FStar_Options.prims ()  in
       let uu____266 =
         FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps  in
       parse_mod uu____264 uu____266  in
     match uu____259 with
     | (dsenv1,prims_mod) ->
         let env1 =
           let uu___423_270 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___423_270.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___423_270.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___423_270.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___423_270.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___423_270.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___423_270.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___423_270.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___423_270.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___423_270.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___423_270.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___423_270.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___423_270.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___423_270.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___423_270.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___423_270.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___423_270.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___423_270.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___423_270.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___423_270.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___423_270.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___423_270.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___423_270.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___423_270.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___423_270.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___423_270.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___423_270.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___423_270.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___423_270.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___423_270.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___423_270.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___423_270.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___423_270.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___423_270.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___423_270.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___423_270.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___423_270.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___423_270.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___423_270.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___423_270.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___423_270.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___423_270.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = dsenv1;
             FStar_TypeChecker_Env.nbe =
               (uu___423_270.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____271 =
           FStar_TypeChecker_Tc.check_module env1 prims_mod false  in
         (match uu____271 with
          | (_prims_mod,uu____282,env2) ->
              let env3 =
                let uu___424_289 = env2  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___424_289.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___424_289.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___424_289.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___424_289.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___424_289.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___424_289.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___424_289.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___424_289.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___424_289.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___424_289.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___424_289.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___424_289.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___424_289.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___424_289.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___424_289.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___424_289.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___424_289.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___424_289.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___424_289.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___424_289.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___424_289.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___424_289.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___424_289.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___424_289.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___424_289.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___424_289.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___424_289.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___424_289.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___424_289.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___424_289.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___424_289.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___424_289.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___424_289.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___424_289.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___424_289.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___424_289.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___424_289.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___424_289.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___424_289.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___424_289.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___424_289.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv = dsenv1;
                  FStar_TypeChecker_Env.nbe =
                    (uu___424_289.FStar_TypeChecker_Env.nbe)
                }  in
              let env4 =
                FStar_TypeChecker_Env.set_current_module env3 test_lid  in
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env4)))
  
let rec (init : unit -> FStar_TypeChecker_Env.env) =
  fun uu____319  ->
    let uu____320 = FStar_ST.op_Bang tcenv_ref  in
    match uu____320 with
    | FStar_Pervasives_Native.Some f -> f
    | uu____347 -> (init_once (); init ())
  
let (frag_of_text : Prims.string -> FStar_Parser_ParseIt.input_frag) =
  fun s  ->
    {
      FStar_Parser_ParseIt.frag_text = s;
      FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
      FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
    }
  
let (pars : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    try
      (fun uu___426_373  ->
         match () with
         | () ->
             let tcenv = init ()  in
             let uu____375 =
               let uu____376 =
                 FStar_All.pipe_left
                   (fun _0_1  -> FStar_Parser_ParseIt.Fragment _0_1)
                   (frag_of_text s)
                  in
               FStar_Parser_ParseIt.parse uu____376  in
             (match uu____375 with
              | FStar_Parser_ParseIt.Term t ->
                  FStar_ToSyntax_ToSyntax.desugar_term
                    tcenv.FStar_TypeChecker_Env.dsenv t
              | FStar_Parser_ParseIt.ParseError (e,msg,r) ->
                  FStar_Errors.raise_error (e, msg) r
              | FStar_Parser_ParseIt.ASTFragment uu____384 ->
                  failwith
                    "Impossible: parsing a Fragment always results in a Term"))
        ()
    with
    | uu___425_398 ->
        if
          let uu____399 = FStar_Options.trace_error ()  in
          Prims.op_Negation uu____399
        then Obj.magic (Obj.repr (FStar_Exn.raise uu___425_398))
        else Obj.magic (Obj.repr (failwith "unreachable"))
  
let (tc' :
  Prims.string ->
    (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t,FStar_TypeChecker_Env.env)
      FStar_Pervasives_Native.tuple3)
  =
  fun s  ->
    let tm = pars s  in
    let tcenv = init ()  in
    let tcenv1 =
      let uu___427_418 = tcenv  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___427_418.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___427_418.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___427_418.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___427_418.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___427_418.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___427_418.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___427_418.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___427_418.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___427_418.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___427_418.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___427_418.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___427_418.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___427_418.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___427_418.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___427_418.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___427_418.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___427_418.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___427_418.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___427_418.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___427_418.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___427_418.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___427_418.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___427_418.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___427_418.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___427_418.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___427_418.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___427_418.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___427_418.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___427_418.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___427_418.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___427_418.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___427_418.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___427_418.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___427_418.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___427_418.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___427_418.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___427_418.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___427_418.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___427_418.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___427_418.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___427_418.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___427_418.FStar_TypeChecker_Env.nbe)
      }  in
    let uu____420 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm
       in
    match uu____420 with | (tm1,uu____434,g) -> (tm1, g, tcenv1)
  
let (tc : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____444 = tc' s  in
    match uu____444 with | (tm,uu____452,uu____453) -> tm
  
let (tc_nbe : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____462 = tc' s  in
    match uu____462 with
    | (tm,g,tcenv) -> (FStar_TypeChecker_Rel.force_trivial_guard tcenv g; tm)
  
let (tc_nbe_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun tm  ->
    let tcenv = init ()  in
    let tcenv1 =
      let uu___428_481 = tcenv  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___428_481.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___428_481.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___428_481.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___428_481.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___428_481.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___428_481.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___428_481.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___428_481.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___428_481.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___428_481.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___428_481.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___428_481.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___428_481.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___428_481.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___428_481.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___428_481.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___428_481.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___428_481.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___428_481.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___428_481.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___428_481.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___428_481.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___428_481.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___428_481.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___428_481.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___428_481.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___428_481.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___428_481.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___428_481.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___428_481.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___428_481.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___428_481.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___428_481.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___428_481.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___428_481.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___428_481.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___428_481.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___428_481.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___428_481.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___428_481.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___428_481.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe = (uu___428_481.FStar_TypeChecker_Env.nbe)
      }  in
    let uu____483 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm
       in
    match uu____483 with
    | (tm1,uu____491,g) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g; tm1)
  
let (pars_and_tc_fragment : Prims.string -> unit) =
  fun s  ->
    FStar_Options.set_option "trace_error" (FStar_Options.Bool true);
    (let report uu____510 =
       let uu____511 = FStar_Errors.report_all ()  in
       FStar_All.pipe_right uu____511 (fun a1  -> ())  in
     try
       (fun uu___430_519  ->
          match () with
          | () ->
              let tcenv = init ()  in
              let frag = frag_of_text s  in
              (try
                 (fun uu___432_531  ->
                    match () with
                    | () ->
                        let uu____532 =
                          let uu____539 = FStar_ST.op_Bang test_mod_ref  in
                          FStar_Universal.tc_one_fragment uu____539 tcenv
                            frag
                           in
                        (match uu____532 with
                         | (test_mod',tcenv') ->
                             (FStar_ST.op_Colon_Equals test_mod_ref test_mod';
                              FStar_ST.op_Colon_Equals tcenv_ref
                                (FStar_Pervasives_Native.Some tcenv');
                              (let n1 = FStar_Errors.get_err_count ()  in
                               if n1 <> (Prims.parse_int "0")
                               then
                                 (report ();
                                  (let uu____625 =
                                     let uu____631 =
                                       let uu____633 =
                                         FStar_Util.string_of_int n1  in
                                       FStar_Util.format1
                                         "%s errors were reported" uu____633
                                        in
                                     (FStar_Errors.Fatal_ErrorsReported,
                                       uu____631)
                                      in
                                   FStar_Errors.raise_err uu____625))
                               else ())))) ()
               with
               | uu___431_641 ->
                   (report ();
                    FStar_Errors.raise_err
                      (FStar_Errors.Fatal_TcOneFragmentFailed,
                        (Prims.strcat "tc_one_fragment failed: " s))))) ()
     with
     | uu___429_646 ->
         if
           let uu____647 = FStar_Options.trace_error ()  in
           Prims.op_Negation uu____647
         then Obj.magic (Obj.repr (FStar_Exn.raise uu___429_646))
         else Obj.magic (Obj.repr (failwith "unreachable")))
  