open Prims
let test_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange
let tcenv_ref:
  FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let test_mod_ref:
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref
    (FStar_Pervasives_Native.Some
       {
         FStar_Syntax_Syntax.name = test_lid;
         FStar_Syntax_Syntax.declarations = [];
         FStar_Syntax_Syntax.exports = [];
         FStar_Syntax_Syntax.is_interface = false
       })
let parse_mod:
  FStar_Parser_ParseIt.filename ->
    FStar_ToSyntax_Env.env ->
      (FStar_ToSyntax_Env.env,FStar_Syntax_Syntax.modul)
        FStar_Pervasives_Native.tuple2
  =
  fun mod_name1  ->
    fun dsenv  ->
      let uu____37 =
        FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename mod_name1) in
      match uu____37 with
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl m,uu____43) ->
          let uu____64 =
            let uu____69 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul m in
            uu____69 dsenv in
          (match uu____64 with
           | (m1,env') ->
               let uu____80 =
                 let uu____85 =
                   FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange in
                 FStar_ToSyntax_Env.prepare_module_or_interface false false
                   env' uu____85 FStar_ToSyntax_Env.default_mii in
               (match uu____80 with | (env'1,uu____91) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (msg,r) ->
          FStar_Exn.raise (FStar_Errors.Error (msg, r))
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr uu____98,uu____99)
          ->
          let msg = FStar_Util.format1 "%s: expected a module\n" mod_name1 in
          FStar_Exn.raise (FStar_Errors.Error (msg, FStar_Range.dummyRange))
      | FStar_Parser_ParseIt.Term uu____127 ->
          failwith
            "Impossible: parsing a Filename always results in an ASTFragment"
let add_mods:
  FStar_Parser_ParseIt.filename Prims.list ->
    FStar_ToSyntax_Env.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_ToSyntax_Env.env,FStar_TypeChecker_Env.env)
          FStar_Pervasives_Native.tuple2
  =
  fun mod_names  ->
    fun dsenv  ->
      fun env  ->
        FStar_List.fold_left
          (fun uu____163  ->
             fun mod_name1  ->
               match uu____163 with
               | (dsenv1,env1) ->
                   let uu____175 = parse_mod mod_name1 dsenv1 in
                   (match uu____175 with
                    | (dsenv2,string_mod) ->
                        let uu____186 =
                          FStar_TypeChecker_Tc.check_module env1 string_mod in
                        (match uu____186 with | (_mod,env2) -> (dsenv2, env2))))
          (dsenv, env) mod_names
let init_once: Prims.unit -> Prims.unit =
  fun uu____199  ->
    let solver1 = FStar_SMTEncoding_Solver.dummy in
    let env =
      FStar_TypeChecker_Env.initial_env FStar_Parser_Dep.empty_deps
        FStar_TypeChecker_TcTerm.tc_term
        FStar_TypeChecker_TcTerm.type_of_tot_term
        FStar_TypeChecker_TcTerm.universe_of solver1
        FStar_Parser_Const.prims_lid in
    (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.init env;
    (let uu____203 =
       let uu____208 = FStar_Options.prims () in
       let uu____209 = FStar_ToSyntax_Env.empty_env () in
       parse_mod uu____208 uu____209 in
     match uu____203 with
     | (dsenv,prims_mod) ->
         let env1 =
           let uu___528_213 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___528_213.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___528_213.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___528_213.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___528_213.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___528_213.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___528_213.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___528_213.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___528_213.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___528_213.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___528_213.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___528_213.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___528_213.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___528_213.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___528_213.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___528_213.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___528_213.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___528_213.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___528_213.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___528_213.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___528_213.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.failhard =
               (uu___528_213.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___528_213.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.tc_term =
               (uu___528_213.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___528_213.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___528_213.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___528_213.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qname_and_index =
               (uu___528_213.FStar_TypeChecker_Env.qname_and_index);
             FStar_TypeChecker_Env.proof_ns =
               (uu___528_213.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth =
               (uu___528_213.FStar_TypeChecker_Env.synth);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___528_213.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___528_213.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___528_213.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = dsenv;
             FStar_TypeChecker_Env.dep_graph =
               (uu___528_213.FStar_TypeChecker_Env.dep_graph)
           } in
         let uu____214 = FStar_TypeChecker_Tc.check_module env1 prims_mod in
         (match uu____214 with
          | (_prims_mod,env2) ->
              let env3 =
                FStar_TypeChecker_Env.set_current_module env2 test_lid in
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env3)))
let rec init: Prims.unit -> FStar_TypeChecker_Env.env =
  fun uu____274  ->
    let uu____275 = FStar_ST.op_Bang tcenv_ref in
    match uu____275 with
    | FStar_Pervasives_Native.Some f -> f
    | uu____329 -> (init_once (); init ())
let frag_of_text: Prims.string -> FStar_Parser_ParseIt.input_frag =
  fun s  ->
    {
      FStar_Parser_ParseIt.frag_text = s;
      FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
      FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
    }
let pars: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    try
      let tcenv = init () in
      let uu____345 =
        let uu____346 =
          FStar_All.pipe_left
            (fun _0_64  -> FStar_Parser_ParseIt.Fragment _0_64)
            (frag_of_text s) in
        FStar_Parser_ParseIt.parse uu____346 in
      match uu____345 with
      | FStar_Parser_ParseIt.Term t ->
          FStar_ToSyntax_ToSyntax.desugar_term
            tcenv.FStar_TypeChecker_Env.dsenv t
      | FStar_Parser_ParseIt.ParseError (msg,r) ->
          FStar_Exn.raise (FStar_Errors.Error (msg, r))
      | FStar_Parser_ParseIt.ASTFragment uu____350 ->
          failwith "Impossible: parsing a Fragment always results in a Term"
    with
    | e when
        let uu____365 = FStar_Options.trace_error () in
        Prims.op_Negation uu____365 -> FStar_Exn.raise e
let tc: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let tm = pars s in
    let tcenv = init () in
    let tcenv1 =
      let uu___531_372 = tcenv in
      {
        FStar_TypeChecker_Env.solver =
          (uu___531_372.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___531_372.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___531_372.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___531_372.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___531_372.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___531_372.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___531_372.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___531_372.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___531_372.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___531_372.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___531_372.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___531_372.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___531_372.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___531_372.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___531_372.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___531_372.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___531_372.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (uu___531_372.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___531_372.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___531_372.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___531_372.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___531_372.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___531_372.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___531_372.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___531_372.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___531_372.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___531_372.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___531_372.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___531_372.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___531_372.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___531_372.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___531_372.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.dep_graph =
          (uu___531_372.FStar_TypeChecker_Env.dep_graph)
      } in
    let uu____373 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm in
    match uu____373 with | (tm1,uu____381,uu____382) -> tm1
let pars_and_tc_fragment: Prims.string -> Prims.unit =
  fun s  ->
    FStar_Options.set_option "trace_error" (FStar_Options.Bool true);
    (let report1 uu____390 =
       let uu____391 = FStar_Errors.report_all () in
       FStar_All.pipe_right uu____391 FStar_Pervasives.ignore in
     try
       let tcenv = init () in
       let frag = frag_of_text s in
       try
         let uu____414 =
           let uu____421 = FStar_ST.op_Bang test_mod_ref in
           FStar_Universal.tc_one_fragment uu____421 tcenv frag in
         match uu____414 with
         | (test_mod',tcenv') ->
             (FStar_ST.op_Colon_Equals test_mod_ref test_mod';
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some tcenv');
              (let n1 = FStar_Errors.get_err_count () in
               if n1 <> (Prims.parse_int "0")
               then
                 (report1 ();
                  (let uu____584 =
                     let uu____585 =
                       let uu____586 = FStar_Util.string_of_int n1 in
                       FStar_Util.format1 "%s errors were reported" uu____586 in
                     FStar_Errors.Err uu____585 in
                   FStar_Exn.raise uu____584))
               else ()))
       with
       | e ->
           (report1 ();
            FStar_Exn.raise
              (FStar_Errors.Err (Prims.strcat "tc_one_fragment failed: " s)))
     with
     | e when
         let uu____598 = FStar_Options.trace_error () in
         Prims.op_Negation uu____598 -> FStar_Exn.raise e)