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
  fun mod_name1  ->
    fun dsenv1  ->
      let uu____83199 =
        FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename mod_name1)
         in
      match uu____83199 with
      | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl m,uu____83205) ->
          let uu____83222 =
            let uu____83227 = FStar_ToSyntax_ToSyntax.ast_modul_to_modul m
               in
            uu____83227 dsenv1  in
          (match uu____83222 with
           | (m1,env') ->
               let uu____83240 =
                 let uu____83246 =
                   FStar_Ident.lid_of_path ["Test"] FStar_Range.dummyRange
                    in
                 FStar_Syntax_DsEnv.prepare_module_or_interface false false
                   env' uu____83246 FStar_Syntax_DsEnv.default_mii
                  in
               (match uu____83240 with | (env'1,uu____83257) -> (env'1, m1)))
      | FStar_Parser_ParseIt.ParseError (err,msg,r) ->
          FStar_Exn.raise (FStar_Errors.Error (err, msg, r))
      | FStar_Parser_ParseIt.ASTFragment
          (FStar_Util.Inr uu____83270,uu____83271) ->
          let msg = FStar_Util.format1 "%s: expected a module\n" mod_name1
             in
          FStar_Errors.raise_error (FStar_Errors.Fatal_ModuleExpected, msg)
            FStar_Range.dummyRange
      | FStar_Parser_ParseIt.Term uu____83298 ->
          failwith
            "Impossible: parsing a Filename always results in an ASTFragment"
  
let (add_mods :
  Prims.string Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_TypeChecker_Env.env ->
        (FStar_Syntax_DsEnv.env * FStar_TypeChecker_Env.env))
  =
  fun mod_names  ->
    fun dsenv1  ->
      fun env  ->
        FStar_List.fold_left
          (fun uu____83345  ->
             fun mod_name1  ->
               match uu____83345 with
               | (dsenv2,env1) ->
                   let uu____83358 = parse_mod mod_name1 dsenv2  in
                   (match uu____83358 with
                    | (dsenv3,string_mod) ->
                        let uu____83369 =
                          FStar_TypeChecker_Tc.check_module env1 string_mod
                            false
                           in
                        (match uu____83369 with
                         | (_mod,env2) -> (dsenv3, env2)))) (dsenv1, env)
          mod_names
  
let (init_once : unit -> unit) =
  fun uu____83386  ->
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
    (let uu____83390 =
       let uu____83395 = FStar_Options.prims ()  in
       let uu____83397 =
         FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps  in
       parse_mod uu____83395 uu____83397  in
     match uu____83390 with
     | (dsenv1,prims_mod) ->
         let env1 =
           let uu___788_83401 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___788_83401.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___788_83401.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___788_83401.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___788_83401.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___788_83401.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___788_83401.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___788_83401.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___788_83401.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___788_83401.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___788_83401.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.is_pattern =
               (uu___788_83401.FStar_TypeChecker_Env.is_pattern);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___788_83401.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___788_83401.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___788_83401.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___788_83401.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___788_83401.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___788_83401.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___788_83401.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.is_iface =
               (uu___788_83401.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___788_83401.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___788_83401.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___788_83401.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___788_83401.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___788_83401.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___788_83401.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___788_83401.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___788_83401.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___788_83401.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___788_83401.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___788_83401.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___788_83401.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___788_83401.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___788_83401.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___788_83401.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___788_83401.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___788_83401.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.splice =
               (uu___788_83401.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.postprocess =
               (uu___788_83401.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___788_83401.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___788_83401.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___788_83401.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv = dsenv1;
             FStar_TypeChecker_Env.nbe =
               (uu___788_83401.FStar_TypeChecker_Env.nbe)
           }  in
         let uu____83402 =
           FStar_TypeChecker_Tc.check_module env1 prims_mod false  in
         (match uu____83402 with
          | (_prims_mod,env2) ->
              let env3 =
                let uu___794_83411 = env2  in
                {
                  FStar_TypeChecker_Env.solver =
                    (uu___794_83411.FStar_TypeChecker_Env.solver);
                  FStar_TypeChecker_Env.range =
                    (uu___794_83411.FStar_TypeChecker_Env.range);
                  FStar_TypeChecker_Env.curmodule =
                    (uu___794_83411.FStar_TypeChecker_Env.curmodule);
                  FStar_TypeChecker_Env.gamma =
                    (uu___794_83411.FStar_TypeChecker_Env.gamma);
                  FStar_TypeChecker_Env.gamma_sig =
                    (uu___794_83411.FStar_TypeChecker_Env.gamma_sig);
                  FStar_TypeChecker_Env.gamma_cache =
                    (uu___794_83411.FStar_TypeChecker_Env.gamma_cache);
                  FStar_TypeChecker_Env.modules =
                    (uu___794_83411.FStar_TypeChecker_Env.modules);
                  FStar_TypeChecker_Env.expected_typ =
                    (uu___794_83411.FStar_TypeChecker_Env.expected_typ);
                  FStar_TypeChecker_Env.sigtab =
                    (uu___794_83411.FStar_TypeChecker_Env.sigtab);
                  FStar_TypeChecker_Env.attrtab =
                    (uu___794_83411.FStar_TypeChecker_Env.attrtab);
                  FStar_TypeChecker_Env.is_pattern =
                    (uu___794_83411.FStar_TypeChecker_Env.is_pattern);
                  FStar_TypeChecker_Env.instantiate_imp =
                    (uu___794_83411.FStar_TypeChecker_Env.instantiate_imp);
                  FStar_TypeChecker_Env.effects =
                    (uu___794_83411.FStar_TypeChecker_Env.effects);
                  FStar_TypeChecker_Env.generalize =
                    (uu___794_83411.FStar_TypeChecker_Env.generalize);
                  FStar_TypeChecker_Env.letrecs =
                    (uu___794_83411.FStar_TypeChecker_Env.letrecs);
                  FStar_TypeChecker_Env.top_level =
                    (uu___794_83411.FStar_TypeChecker_Env.top_level);
                  FStar_TypeChecker_Env.check_uvars =
                    (uu___794_83411.FStar_TypeChecker_Env.check_uvars);
                  FStar_TypeChecker_Env.use_eq =
                    (uu___794_83411.FStar_TypeChecker_Env.use_eq);
                  FStar_TypeChecker_Env.is_iface =
                    (uu___794_83411.FStar_TypeChecker_Env.is_iface);
                  FStar_TypeChecker_Env.admit =
                    (uu___794_83411.FStar_TypeChecker_Env.admit);
                  FStar_TypeChecker_Env.lax =
                    (uu___794_83411.FStar_TypeChecker_Env.lax);
                  FStar_TypeChecker_Env.lax_universes =
                    (uu___794_83411.FStar_TypeChecker_Env.lax_universes);
                  FStar_TypeChecker_Env.phase1 =
                    (uu___794_83411.FStar_TypeChecker_Env.phase1);
                  FStar_TypeChecker_Env.failhard =
                    (uu___794_83411.FStar_TypeChecker_Env.failhard);
                  FStar_TypeChecker_Env.nosynth =
                    (uu___794_83411.FStar_TypeChecker_Env.nosynth);
                  FStar_TypeChecker_Env.uvar_subtyping =
                    (uu___794_83411.FStar_TypeChecker_Env.uvar_subtyping);
                  FStar_TypeChecker_Env.tc_term =
                    (uu___794_83411.FStar_TypeChecker_Env.tc_term);
                  FStar_TypeChecker_Env.type_of =
                    (uu___794_83411.FStar_TypeChecker_Env.type_of);
                  FStar_TypeChecker_Env.universe_of =
                    (uu___794_83411.FStar_TypeChecker_Env.universe_of);
                  FStar_TypeChecker_Env.check_type_of =
                    (uu___794_83411.FStar_TypeChecker_Env.check_type_of);
                  FStar_TypeChecker_Env.use_bv_sorts =
                    (uu___794_83411.FStar_TypeChecker_Env.use_bv_sorts);
                  FStar_TypeChecker_Env.qtbl_name_and_index =
                    (uu___794_83411.FStar_TypeChecker_Env.qtbl_name_and_index);
                  FStar_TypeChecker_Env.normalized_eff_names =
                    (uu___794_83411.FStar_TypeChecker_Env.normalized_eff_names);
                  FStar_TypeChecker_Env.fv_delta_depths =
                    (uu___794_83411.FStar_TypeChecker_Env.fv_delta_depths);
                  FStar_TypeChecker_Env.proof_ns =
                    (uu___794_83411.FStar_TypeChecker_Env.proof_ns);
                  FStar_TypeChecker_Env.synth_hook =
                    (uu___794_83411.FStar_TypeChecker_Env.synth_hook);
                  FStar_TypeChecker_Env.splice =
                    (uu___794_83411.FStar_TypeChecker_Env.splice);
                  FStar_TypeChecker_Env.postprocess =
                    (uu___794_83411.FStar_TypeChecker_Env.postprocess);
                  FStar_TypeChecker_Env.is_native_tactic =
                    (uu___794_83411.FStar_TypeChecker_Env.is_native_tactic);
                  FStar_TypeChecker_Env.identifier_info =
                    (uu___794_83411.FStar_TypeChecker_Env.identifier_info);
                  FStar_TypeChecker_Env.tc_hooks =
                    (uu___794_83411.FStar_TypeChecker_Env.tc_hooks);
                  FStar_TypeChecker_Env.dsenv = dsenv1;
                  FStar_TypeChecker_Env.nbe =
                    (uu___794_83411.FStar_TypeChecker_Env.nbe)
                }  in
              let env4 =
                FStar_TypeChecker_Env.set_current_module env3 test_lid  in
              FStar_ST.op_Colon_Equals tcenv_ref
                (FStar_Pervasives_Native.Some env4)))
  
let (uu___798 : unit) = FStar_Main.setup_hooks (); init_once () 
let (init : unit -> FStar_TypeChecker_Env.env) =
  fun uu____83443  ->
    let uu____83444 = FStar_ST.op_Bang tcenv_ref  in
    match uu____83444 with
    | FStar_Pervasives_Native.Some f -> f
    | uu____83471 ->
        failwith
          "Should have already been initialized by the top-level effect"
  
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
      (fun uu___807_83497  ->
         match () with
         | () ->
             let tcenv = init ()  in
             let uu____83499 =
               let uu____83500 =
                 FStar_All.pipe_left
                   (fun _83501  -> FStar_Parser_ParseIt.Fragment _83501)
                   (frag_of_text s)
                  in
               FStar_Parser_ParseIt.parse uu____83500  in
             (match uu____83499 with
              | FStar_Parser_ParseIt.Term t ->
                  FStar_ToSyntax_ToSyntax.desugar_term
                    tcenv.FStar_TypeChecker_Env.dsenv t
              | FStar_Parser_ParseIt.ParseError (e,msg,r) ->
                  FStar_Errors.raise_error (e, msg) r
              | FStar_Parser_ParseIt.ASTFragment uu____83509 ->
                  failwith
                    "Impossible: parsing a Fragment always results in a Term"))
        ()
    with
    | uu___806_83523 ->
        if
          let uu____83524 = FStar_Options.trace_error ()  in
          Prims.op_Negation uu____83524
        then Obj.magic (Obj.repr (FStar_Exn.raise uu___806_83523))
        else Obj.magic (Obj.repr (failwith "unreachable"))
  
let (tc' :
  Prims.string ->
    (FStar_Syntax_Syntax.term * FStar_TypeChecker_Env.guard_t *
      FStar_TypeChecker_Env.env))
  =
  fun s  ->
    let tm = pars s  in
    let tcenv = init ()  in
    let tcenv1 =
      let uu___825_83543 = tcenv  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___825_83543.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___825_83543.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___825_83543.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___825_83543.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___825_83543.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___825_83543.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___825_83543.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___825_83543.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___825_83543.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___825_83543.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___825_83543.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___825_83543.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___825_83543.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___825_83543.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___825_83543.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___825_83543.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___825_83543.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___825_83543.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___825_83543.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___825_83543.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___825_83543.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___825_83543.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___825_83543.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___825_83543.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___825_83543.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___825_83543.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___825_83543.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___825_83543.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___825_83543.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___825_83543.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___825_83543.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___825_83543.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___825_83543.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___825_83543.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___825_83543.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___825_83543.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___825_83543.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___825_83543.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___825_83543.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___825_83543.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___825_83543.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___825_83543.FStar_TypeChecker_Env.nbe)
      }  in
    let uu____83545 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm
       in
    match uu____83545 with | (tm1,uu____83559,g) -> (tm1, g, tcenv1)
  
let (tc : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____83569 = tc' s  in
    match uu____83569 with | (tm,uu____83577,uu____83578) -> tm
  
let (tc_nbe : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____83587 = tc' s  in
    match uu____83587 with
    | (tm,g,tcenv) -> (FStar_TypeChecker_Rel.force_trivial_guard tcenv g; tm)
  
let (tc_nbe_term : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun tm  ->
    let tcenv = init ()  in
    let tcenv1 =
      let uu___845_83606 = tcenv  in
      {
        FStar_TypeChecker_Env.solver =
          (uu___845_83606.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___845_83606.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___845_83606.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___845_83606.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___845_83606.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___845_83606.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___845_83606.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___845_83606.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___845_83606.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___845_83606.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___845_83606.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___845_83606.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___845_83606.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___845_83606.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___845_83606.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level = false;
        FStar_TypeChecker_Env.check_uvars =
          (uu___845_83606.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___845_83606.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___845_83606.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___845_83606.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax =
          (uu___845_83606.FStar_TypeChecker_Env.lax);
        FStar_TypeChecker_Env.lax_universes =
          (uu___845_83606.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___845_83606.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___845_83606.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___845_83606.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___845_83606.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___845_83606.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___845_83606.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___845_83606.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___845_83606.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___845_83606.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___845_83606.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___845_83606.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___845_83606.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___845_83606.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___845_83606.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___845_83606.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___845_83606.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___845_83606.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___845_83606.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___845_83606.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv =
          (uu___845_83606.FStar_TypeChecker_Env.dsenv);
        FStar_TypeChecker_Env.nbe =
          (uu___845_83606.FStar_TypeChecker_Env.nbe)
      }  in
    let uu____83608 = FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term tcenv1 tm
       in
    match uu____83608 with
    | (tm1,uu____83616,g) ->
        (FStar_TypeChecker_Rel.force_trivial_guard tcenv1 g; tm1)
  
let (pars_and_tc_fragment : Prims.string -> unit) =
  fun s  ->
    FStar_Options.set_option "trace_error" (FStar_Options.Bool true);
    (let report uu____83635 =
       let uu____83636 = FStar_Errors.report_all ()  in
       FStar_All.pipe_right uu____83636 (fun a1  -> ())  in
     try
       (fun uu___858_83644  ->
          match () with
          | () ->
              let tcenv = init ()  in
              let frag = frag_of_text s  in
              (try
                 (fun uu___866_83656  ->
                    match () with
                    | () ->
                        let uu____83657 =
                          let uu____83664 = FStar_ST.op_Bang test_mod_ref  in
                          FStar_Universal.tc_one_fragment uu____83664 tcenv
                            frag
                           in
                        (match uu____83657 with
                         | (test_mod',tcenv') ->
                             (FStar_ST.op_Colon_Equals test_mod_ref test_mod';
                              FStar_ST.op_Colon_Equals tcenv_ref
                                (FStar_Pervasives_Native.Some tcenv');
                              (let n1 = FStar_Errors.get_err_count ()  in
                               if n1 <> (Prims.parse_int "0")
                               then
                                 (report ();
                                  (let uu____83750 =
                                     let uu____83756 =
                                       let uu____83758 =
                                         FStar_Util.string_of_int n1  in
                                       FStar_Util.format1
                                         "%s errors were reported"
                                         uu____83758
                                        in
                                     (FStar_Errors.Fatal_ErrorsReported,
                                       uu____83756)
                                      in
                                   FStar_Errors.raise_err uu____83750))
                               else ())))) ()
               with
               | uu___865_83766 ->
                   (report ();
                    FStar_Errors.raise_err
                      (FStar_Errors.Fatal_TcOneFragmentFailed,
                        (Prims.op_Hat "tc_one_fragment failed: " s))))) ()
     with
     | uu___857_83771 ->
         if
           let uu____83772 = FStar_Options.trace_error ()  in
           Prims.op_Negation uu____83772
         then Obj.magic (Obj.repr (FStar_Exn.raise uu___857_83771))
         else Obj.magic (Obj.repr (failwith "unreachable")))
  