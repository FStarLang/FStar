open Prims
type push_kind =
  | SyntaxCheck 
  | LaxCheck 
  | FullCheck 
let (uu___is_SyntaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | SyntaxCheck -> true | uu____8 -> false
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | LaxCheck -> true | uu____19 -> false
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | FullCheck -> true | uu____30 -> false
type ctx_depth_t =
  (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int)
let (repl_stack : FStar_JsonHelper.repl_stack_t FStar_ST.ref) =
  FStar_Util.mk_ref []
let (set_check_kind :
  FStar_TypeChecker_Env.env_t -> push_kind -> FStar_TypeChecker_Env.env_t) =
  fun env ->
    fun check_kind ->
      let uu___2_67 = env in
      let uu____68 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___2_67.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (uu___2_67.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___2_67.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (uu___2_67.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___2_67.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___2_67.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___2_67.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___2_67.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___2_67.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___2_67.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___2_67.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___2_67.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___2_67.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___2_67.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___2_67.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___2_67.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___2_67.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___2_67.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___2_67.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (uu___2_67.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___2_67.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___2_67.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___2_67.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___2_67.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___2_67.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___2_67.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___2_67.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___2_67.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___2_67.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___2_67.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___2_67.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___2_67.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___2_67.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___2_67.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___2_67.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___2_67.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___2_67.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___2_67.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___2_67.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___2_67.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____68;
        FStar_TypeChecker_Env.nbe = (uu___2_67.FStar_TypeChecker_Env.nbe)
      }
let (snapshot_env :
  FStar_TypeChecker_Env.env_t ->
    Prims.string ->
      (FStar_JsonHelper.repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun msg ->
      let uu____90 = FStar_TypeChecker_Tc.snapshot_context env msg in
      match uu____90 with
      | (ctx_depth, env1) ->
          let uu____134 = FStar_Options.snapshot () in
          (match uu____134 with
           | (opt_depth, ()) -> ((ctx_depth, opt_depth), env1))
let (push_repl :
  Prims.string ->
    push_kind ->
      FStar_JsonHelper.repl_task ->
        FStar_JsonHelper.repl_state -> FStar_JsonHelper.repl_state)
  =
  fun msg ->
    fun push_kind ->
      fun task ->
        fun st ->
          let uu____171 = snapshot_env st.FStar_JsonHelper.repl_env msg in
          match uu____171 with
          | (depth, env) ->
              ((let uu____179 =
                  let uu____180 = FStar_ST.op_Bang repl_stack in
                  (depth, (task, st)) :: uu____180 in
                FStar_ST.op_Colon_Equals repl_stack uu____179);
               (let uu___20_241 = st in
                let uu____242 = set_check_kind env push_kind in
                {
                  FStar_JsonHelper.repl_line =
                    (uu___20_241.FStar_JsonHelper.repl_line);
                  FStar_JsonHelper.repl_column =
                    (uu___20_241.FStar_JsonHelper.repl_column);
                  FStar_JsonHelper.repl_fname =
                    (uu___20_241.FStar_JsonHelper.repl_fname);
                  FStar_JsonHelper.repl_deps_stack =
                    (uu___20_241.FStar_JsonHelper.repl_deps_stack);
                  FStar_JsonHelper.repl_curmod =
                    (uu___20_241.FStar_JsonHelper.repl_curmod);
                  FStar_JsonHelper.repl_env = uu____242;
                  FStar_JsonHelper.repl_stdin =
                    (uu___20_241.FStar_JsonHelper.repl_stdin);
                  FStar_JsonHelper.repl_names =
                    (uu___20_241.FStar_JsonHelper.repl_names)
                }))
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string -> (ctx_depth_t * Prims.int) -> FStar_TypeChecker_Env.env_t)
  =
  fun solver1 ->
    fun msg ->
      fun uu____264 ->
        match uu____264 with
        | (ctx_depth, opt_depth) ->
            let env =
              FStar_TypeChecker_Tc.rollback_context solver1 msg
                (FStar_Pervasives_Native.Some ctx_depth) in
            (FStar_Options.rollback (FStar_Pervasives_Native.Some opt_depth);
             env)
let (pop_repl :
  Prims.string -> FStar_JsonHelper.repl_state -> FStar_JsonHelper.repl_state)
  =
  fun msg ->
    fun st ->
      let uu____302 = FStar_ST.op_Bang repl_stack in
      match uu____302 with
      | [] -> failwith "Too many pops"
      | (depth, (uu____332, st'))::stack_tl ->
          let env =
            rollback_env
              (st.FStar_JsonHelper.repl_env).FStar_TypeChecker_Env.solver msg
              depth in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____379 =
              FStar_Util.physical_equality env st'.FStar_JsonHelper.repl_env in
            FStar_Common.runtime_assert uu____379 "Inconsistent stack state");
           st')
let (tc_one :
  FStar_TypeChecker_Env.env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> FStar_TypeChecker_Env.env_t)
  =
  fun env ->
    fun intf_opt ->
      fun modf ->
        let parse_data =
          let uu____407 =
            let uu____413 = FStar_TypeChecker_Env.dep_graph env in
            FStar_Parser_Dep.parsing_data_of uu____413 in
          FStar_All.pipe_right modf uu____407 in
        let uu____415 =
          FStar_Universal.tc_one_file_for_ide env intf_opt modf parse_data in
        match uu____415 with | (uu____420, env1) -> env1
let (run_repl_task :
  FStar_JsonHelper.optmod_t ->
    FStar_TypeChecker_Env.env_t ->
      FStar_JsonHelper.repl_task ->
        (FStar_JsonHelper.optmod_t * FStar_TypeChecker_Env.env_t))
  =
  fun curmod ->
    fun env ->
      fun task ->
        match task with
        | FStar_JsonHelper.LDInterleaved (intf, impl) ->
            let uu____448 =
              tc_one env
                (FStar_Pervasives_Native.Some
                   (intf.FStar_JsonHelper.tf_fname))
                impl.FStar_JsonHelper.tf_fname in
            (curmod, uu____448)
        | FStar_JsonHelper.LDSingle intf_or_impl ->
            let uu____451 =
              tc_one env FStar_Pervasives_Native.None
                intf_or_impl.FStar_JsonHelper.tf_fname in
            (curmod, uu____451)
        | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
            let uu____454 =
              FStar_Universal.load_interface_decls env
                intf.FStar_JsonHelper.tf_fname in
            (curmod, uu____454)
        | FStar_JsonHelper.PushFragment frag ->
            FStar_Universal.tc_one_fragment curmod env frag
        | FStar_JsonHelper.Noop -> (curmod, env)
let (repl_tx :
  FStar_JsonHelper.repl_state ->
    push_kind ->
      FStar_JsonHelper.repl_task ->
        (Prims.bool * FStar_JsonHelper.repl_state))
  =
  fun st ->
    fun push_kind ->
      fun task ->
        let st1 = push_repl "repl_tx" push_kind task st in
        let check_success uu____485 =
          let uu____486 = FStar_Errors.get_err_count () in
          uu____486 = (Prims.parse_int "0") in
        try
          (fun uu___70_500 ->
             match () with
             | () ->
                 let uu____506 =
                   run_repl_task st1.FStar_JsonHelper.repl_curmod
                     st1.FStar_JsonHelper.repl_env task in
                 (match uu____506 with
                  | (curmod, env) ->
                      let st2 =
                        let uu___78_519 = st1 in
                        {
                          FStar_JsonHelper.repl_line =
                            (uu___78_519.FStar_JsonHelper.repl_line);
                          FStar_JsonHelper.repl_column =
                            (uu___78_519.FStar_JsonHelper.repl_column);
                          FStar_JsonHelper.repl_fname =
                            (uu___78_519.FStar_JsonHelper.repl_fname);
                          FStar_JsonHelper.repl_deps_stack =
                            (uu___78_519.FStar_JsonHelper.repl_deps_stack);
                          FStar_JsonHelper.repl_curmod = curmod;
                          FStar_JsonHelper.repl_env = env;
                          FStar_JsonHelper.repl_stdin =
                            (uu___78_519.FStar_JsonHelper.repl_stdin);
                          FStar_JsonHelper.repl_names =
                            (uu___78_519.FStar_JsonHelper.repl_names)
                        } in
                      (true, st2))) ()
        with
        | uu___69_524 ->
            let uu____530 = pop_repl "run_tx" st1 in (false, uu____530)