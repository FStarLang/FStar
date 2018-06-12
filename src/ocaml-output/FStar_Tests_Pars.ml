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
      let uu____49 =
        FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename mod_name1)
         in
      match uu____49 with
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl m,uu____55) ->
          let uu____70 =
            let uu____75 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul m  in
            uu____75 dsenv1  in
          (match uu____70 with
           | (m1,env') ->
               let uu____88 =
                 let uu____93 =
                   FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange
                    in
                 FStar_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu____93 FStar_Syntax_DsEnv.default_mii
                  in
               (match uu____88 with | (env'1,uu____99) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (err,msg,r) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, r))
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr uu____107,uu____108)
          ->
          let msg = FStar_Util.format1 "%s: expected a module\n" mod_name1
             in
          FStar_Errors.raise_error (FStar_Errors.Fatal_ModuleExpected, msg)
            FStar_Range.dummyRange
      | FStar_Parser_ParseIt.Term uu____130 ->
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
          (fun uu____173  ->
             fun mod_name1  ->
               match uu____173 with
               | (dsenv2,env1) ->
                   let uu____185 = parse_mod mod_name1 dsenv2  in
                   (match uu____185 with
                    | (dsenv3,string_mod) ->
                        let uu____196 =
                          FStar_TypeChecker_Tc.check_module env1 string_mod
                            false
                           in
                        (match uu____196 with
                         | (_mod,uu____210,env2) -> (dsenv3, env2))))
          (dsenv1, env) mod_names
  
let (init_once : unit -> unit) =
  fun uu____220  ->
    let solver1 = FStar_SMTEncoding_Solver.dummy  in
    let env =
      FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps
        FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of
        FStar_TypeChecker_TcTerm.check_type_of_well_typed_term solver1
        FStar_Parser_Const.prims_lid
       in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let uu____224 =
       let uu____229 = FStar_Options.prims ()  in
       let uu____230 = FStar_Syntax_DsEnv.empty_env ()  in
       parse_mod uu____229 uu____230  in
     match uu____224 with
     | (dsenv1,prims_mod) ->
         let env1 =
           let uu___401_234 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___401_234.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___401_234.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___401_234.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___401_234.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___401_234.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___401_234.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___401_234.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___401_234.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___401_234.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___401_234.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___401_234.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___401_234.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___401_234.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___401_234.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___401_234.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___401_234.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___401_234.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___401_234.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___401_234.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___401_234.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___401_234.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___401_234.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___401_234.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___401_234.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___401_234.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___401_234.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___401_234.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___401_234.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___401_234.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___401_234.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___401_234.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___401_234.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.proof_ns =
               (uu___401_234.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___401_234.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___401_234.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___401_234.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___401_234.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___401_234.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = dsenv1;
             FStar_TypeChecker_Env.dep_graph =
               (uu___401_234.FStar_TypeChecker_Env.dep_graph)
           }  in
         let uu____235 =
           FStar_TypeChecker_Tc.check_module env1 prims_mod false  in
         (match uu____235 with
          | (_prims_mod,uu____245,env2) ->
              let env3 =
                FStar_TypeChecker_Env.set_current_module env2 test_lid  in
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env3)))
  
let rec (init : unit -> FStar_TypeChecker_Env.env) =
  fun uu____283  ->
    let uu____284 = FStar_ST.op_Bang tcenv_ref  in
    match uu____284 with
    | FStar_Pervasives_Native.Some f -> f
    | uu____315 -> (init_once (); init ())
  
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
      let tcenv = init ()  in
      let uu____335 =
        let uu____336 =
          FStar_All.pipe_left
            (fun _0_16  -> FStar_Parser_ParseIt.Fragment _0_16)
            (frag_of_text s)
           in
        FStar_Parser_ParseIt.parse uu____336  in
      match uu____335 with
      | FStar_Parser_ParseIt.Term t ->
          FStar_ToSyntax_ToSyntax.desugar_term
            tcenv.FStar_TypeChecker_Env.dsenv t
      | FStar_Parser_ParseIt.ParseError (e,msg,r) ->
          FStar_Errors.raise_error (e, msg) r
      | FStar_Parser_ParseIt.ASTFragment uu____341 ->
          failwith "Impossible: parsing a Fragment always results in a Term"
    with
    | e when
        let uu____356 = FStar_Options.trace_error ()  in
        Prims.op_Negation uu____356 -> FStar_Exn.raise e
  
let (tc : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let tm = pars s  in
    let tcenv = init ()  in
    let tcenv1 =
      let uu___404_365 = tcenv  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___404_365.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___404_365.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___404_365.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___404_365.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___404_365.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___404_365.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___404_365.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___404_365.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___404_365.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___404_365.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___404_365.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___404_365.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___404_365.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___404_365.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___404_365.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___404_365.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___404_365.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___404_365.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___404_365.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___404_365.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___404_365.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___404_365.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___404_365.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___404_365.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___404_365.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___404_365.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___404_365.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___404_365.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___404_365.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___404_365.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___404_365.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.proof_ns =
          (uu___404_365.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___404_365.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___404_365.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___404_365.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___404_365.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___404_365.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___404_365.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___404_365.FStar_TypeChecker_Env.dep_graph)
      }  in
    let uu____366 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm
       in
    match uu____366 with | (tm1,uu____374,uu____375) -> tm1
  
let (pars_and_tc_fragment : Prims.string -> unit) =
  fun s  ->
    FStar_Options.set_option "trace_error" (FStar_Options.Bool true);
    (let report uu____387 =
       let uu____388 = FStar_Errors.report_all ()  in
       FStar_All.pipe_right uu____388 (fun a237  -> ())  in
     try
       let tcenv = init ()  in
       let frag = frag_of_text s  in
       try
         let uu____409 =
           let uu____416 = FStar_ST.op_Bang test_mod_ref  in
           FStar_Universal.tc_one_fragment uu____416 tcenv frag  in
         match uu____409 with
         | (test_mod',tcenv') ->
             (FStar_ST.op_Colon_Equals test_mod_ref test_mod';
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some tcenv');
              (let n1 = FStar_Errors.get_err_count ()  in
               if n1 <> (Prims.parse_int "0")
               then
                 (report ();
                  (let uu____510 =
                     let uu____515 =
                       let uu____516 = FStar_Util.string_of_int n1  in
                       FStar_Util.format1 "%s errors were reported" uu____516
                        in
                     (FStar_Errors.Fatal_ErrorsReported, uu____515)  in
                   FStar_Errors.raise_err uu____510))
               else ()))
       with
       | e ->
           (report ();
            FStar_Errors.raise_err
              (FStar_Errors.Fatal_TcOneFragmentFailed,
                (Prims.strcat "tc_one_fragment failed: " s)))
     with
     | e when
         let uu____528 = FStar_Options.trace_error ()  in
         Prims.op_Negation uu____528 -> FStar_Exn.raise e)
  