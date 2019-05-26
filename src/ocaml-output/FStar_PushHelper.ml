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
type deps_t = FStar_Parser_Dep.deps
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
let (repl_ld_tasks_of_deps :
  Prims.string Prims.list ->
    FStar_JsonHelper.repl_task Prims.list ->
      FStar_JsonHelper.repl_task Prims.list)
  =
  fun deps ->
    fun final_tasks ->
      let wrap fname =
        let uu____100 = FStar_Util.now () in
        {
          FStar_JsonHelper.tf_fname = fname;
          FStar_JsonHelper.tf_modtime = uu____100
        } in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____136 =
              let uu____137 =
                let uu____142 = wrap intf in
                let uu____143 = wrap impl in (uu____142, uu____143) in
              FStar_JsonHelper.LDInterleaved uu____137 in
            let uu____144 = aux deps' final_tasks1 in uu____136 :: uu____144
        | intf_or_impl::deps' ->
            let uu____154 =
              let uu____155 = wrap intf_or_impl in
              FStar_JsonHelper.LDSingle uu____155 in
            let uu____156 = aux deps' final_tasks1 in uu____154 :: uu____156
        | [] -> final_tasks1 in
      aux deps final_tasks
let (deps_and_repl_ld_tasks_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * FStar_JsonHelper.repl_task Prims.list *
      deps_t))
  =
  fun filename ->
    let get_mod_name fname = FStar_Parser_Dep.lowercase_module_name fname in
    let our_mod_name = get_mod_name filename in
    let has_our_mod_name f =
      let uu____210 = get_mod_name f in uu____210 = our_mod_name in
    let parse_data_cache = FStar_CheckedFiles.load_parsing_data_from_cache in
    let uu____221 =
      FStar_Dependencies.find_deps_if_needed [filename] parse_data_cache in
    match uu____221 with
    | (deps, dep_graph1) ->
        let uu____250 = FStar_List.partition has_our_mod_name deps in
        (match uu____250 with
         | (same_name, real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____300 =
                       let uu____302 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu____302 in
                     if uu____300
                     then
                       let uu____305 =
                         let uu____311 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.Fatal_MissingInterface, uu____311) in
                       FStar_Errors.raise_err uu____305
                     else ());
                    (let uu____318 =
                       let uu____320 =
                         FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu____320 in
                     if uu____318
                     then
                       let uu____323 =
                         let uu____329 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____329) in
                       FStar_Errors.raise_err uu____323
                     else ());
                    (let uu____335 =
                       let uu____336 =
                         let uu____337 = FStar_Util.now () in
                         {
                           FStar_JsonHelper.tf_fname = intf;
                           FStar_JsonHelper.tf_modtime = uu____337
                         } in
                       FStar_JsonHelper.LDInterfaceOfCurrentFile uu____336 in
                     [uu____335]))
               | impl::[] -> []
               | uu____342 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu____353 =
                       let uu____359 =
                         FStar_Util.format message [our_mod_name; mods_str] in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____359) in
                     FStar_Errors.raise_err uu____353);
                    []) in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
             (real_deps, tasks, dep_graph1))
let (ld_deps : FStar_JsonHelper.repl_state -> Prims.string Prims.list) =
  fun st ->
    try
      (fun uu___50_390 ->
         match () with
         | () ->
             let uu____394 =
               deps_and_repl_ld_tasks_of_our_file
                 st.FStar_JsonHelper.repl_fname in
             (match uu____394 with | (deps, uu____410, uu____411) -> deps))
        ()
    with
    | uu___49_424 -> (FStar_Util.print_error "[E] Failed to load deps"; [])
let (snapshot_env :
  FStar_TypeChecker_Env.env_t ->
    Prims.string ->
      (FStar_JsonHelper.repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun msg ->
      let uu____452 = FStar_TypeChecker_Tc.snapshot_context env msg in
      match uu____452 with
      | (ctx_depth, env1) ->
          let uu____496 = FStar_Options.snapshot () in
          (match uu____496 with
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
          let uu____533 = snapshot_env st.FStar_JsonHelper.repl_env msg in
          match uu____533 with
          | (depth, env) ->
              ((let uu____541 =
                  let uu____542 = FStar_ST.op_Bang repl_stack in
                  (depth, (task, st)) :: uu____542 in
                FStar_ST.op_Colon_Equals repl_stack uu____541);
               (let uu___76_603 = st in
                let uu____604 = set_check_kind env push_kind in
                {
                  FStar_JsonHelper.repl_line =
                    (uu___76_603.FStar_JsonHelper.repl_line);
                  FStar_JsonHelper.repl_column =
                    (uu___76_603.FStar_JsonHelper.repl_column);
                  FStar_JsonHelper.repl_fname =
                    (uu___76_603.FStar_JsonHelper.repl_fname);
                  FStar_JsonHelper.repl_deps_stack =
                    (uu___76_603.FStar_JsonHelper.repl_deps_stack);
                  FStar_JsonHelper.repl_curmod =
                    (uu___76_603.FStar_JsonHelper.repl_curmod);
                  FStar_JsonHelper.repl_env = uu____604;
                  FStar_JsonHelper.repl_stdin =
                    (uu___76_603.FStar_JsonHelper.repl_stdin);
                  FStar_JsonHelper.repl_names =
                    (uu___76_603.FStar_JsonHelper.repl_names)
                }))
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string -> (ctx_depth_t * Prims.int) -> FStar_TypeChecker_Env.env_t)
  =
  fun solver1 ->
    fun msg ->
      fun uu____626 ->
        match uu____626 with
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
      let uu____664 = FStar_ST.op_Bang repl_stack in
      match uu____664 with
      | [] -> failwith "Too many pops"
      | (depth, (uu____694, st'))::stack_tl ->
          let env =
            rollback_env
              (st.FStar_JsonHelper.repl_env).FStar_TypeChecker_Env.solver msg
              depth in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____741 =
              FStar_Util.physical_equality env st'.FStar_JsonHelper.repl_env in
            FStar_Common.runtime_assert uu____741 "Inconsistent stack state");
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
          let uu____769 =
            let uu____775 = FStar_TypeChecker_Env.dep_graph env in
            FStar_Parser_Dep.parsing_data_of uu____775 in
          FStar_All.pipe_right modf uu____769 in
        let uu____777 =
          FStar_Universal.tc_one_file_for_ide env intf_opt modf parse_data in
        match uu____777 with | (uu____782, env1) -> env1
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
            let uu____810 =
              tc_one env
                (FStar_Pervasives_Native.Some
                   (intf.FStar_JsonHelper.tf_fname))
                impl.FStar_JsonHelper.tf_fname in
            (curmod, uu____810)
        | FStar_JsonHelper.LDSingle intf_or_impl ->
            let uu____813 =
              tc_one env FStar_Pervasives_Native.None
                intf_or_impl.FStar_JsonHelper.tf_fname in
            (curmod, uu____813)
        | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
            let uu____816 =
              FStar_Universal.load_interface_decls env
                intf.FStar_JsonHelper.tf_fname in
            (curmod, uu____816)
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
        try
          (fun uu___124_851 ->
             match () with
             | () ->
                 let uu____857 =
                   run_repl_task st1.FStar_JsonHelper.repl_curmod
                     st1.FStar_JsonHelper.repl_env task in
                 (match uu____857 with
                  | (curmod, env) ->
                      let st2 =
                        let uu___149_870 = st1 in
                        {
                          FStar_JsonHelper.repl_line =
                            (uu___149_870.FStar_JsonHelper.repl_line);
                          FStar_JsonHelper.repl_column =
                            (uu___149_870.FStar_JsonHelper.repl_column);
                          FStar_JsonHelper.repl_fname =
                            (uu___149_870.FStar_JsonHelper.repl_fname);
                          FStar_JsonHelper.repl_deps_stack =
                            (uu___149_870.FStar_JsonHelper.repl_deps_stack);
                          FStar_JsonHelper.repl_curmod = curmod;
                          FStar_JsonHelper.repl_env = env;
                          FStar_JsonHelper.repl_stdin =
                            (uu___149_870.FStar_JsonHelper.repl_stdin);
                          FStar_JsonHelper.repl_names =
                            (uu___149_870.FStar_JsonHelper.repl_names)
                        } in
                      (true, st2))) ()
        with
        | FStar_All.Failure msg ->
            (FStar_Util.print1_error "[F] %s" msg;
             (let uu____887 = pop_repl "run_tx" st1 in (false, uu____887)))
        | FStar_Util.SigInt ->
            (FStar_Util.print_error "[E] Interrupt";
             (let uu____893 = pop_repl "run_tx" st1 in (false, uu____893)))
        | FStar_Errors.Error (e, msg, r) ->
            (FStar_Util.print1_error "[E] %s" msg;
             (let uu____904 = pop_repl "run_tx" st1 in (false, uu____904)))
        | FStar_Errors.Err (e, msg) ->
            (FStar_Util.print1_error "[E] %s" msg;
             (let uu____914 = pop_repl "run_tx" st1 in (false, uu____914)))
        | FStar_Errors.Stop ->
            (FStar_Util.print_error "[E] Stop";
             (let uu____920 = pop_repl "run_tx" st1 in (false, uu____920)))
let (full_lax :
  Prims.string -> FStar_JsonHelper.repl_state -> FStar_JsonHelper.repl_state)
  =
  fun text ->
    fun st ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_text = text;
          FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
          FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
        } in
      let uu____940 =
        repl_tx st LaxCheck (FStar_JsonHelper.PushFragment frag) in
      match uu____940 with | (uu____946, st1) -> st1