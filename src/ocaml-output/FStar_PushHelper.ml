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
type either_replst =
  (FStar_JsonHelper.repl_state, FStar_JsonHelper.repl_state)
    FStar_Util.either
let (repl_stack : FStar_JsonHelper.repl_stack_t FStar_ST.ref) =
  FStar_Util.mk_ref []
let (set_check_kind :
  FStar_TypeChecker_Env.env_t -> push_kind -> FStar_TypeChecker_Env.env_t) =
  fun env ->
    fun check_kind ->
      let uu___4_71 = env in
      let uu____72 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___4_71.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (uu___4_71.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___4_71.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (uu___4_71.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___4_71.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___4_71.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___4_71.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___4_71.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___4_71.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___4_71.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___4_71.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___4_71.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___4_71.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___4_71.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___4_71.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___4_71.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___4_71.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___4_71.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___4_71.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (uu___4_71.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___4_71.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___4_71.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___4_71.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___4_71.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___4_71.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___4_71.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___4_71.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___4_71.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___4_71.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___4_71.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___4_71.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___4_71.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___4_71.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___4_71.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___4_71.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___4_71.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___4_71.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___4_71.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___4_71.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___4_71.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____72;
        FStar_TypeChecker_Env.nbe = (uu___4_71.FStar_TypeChecker_Env.nbe)
      }
let (repl_ld_tasks_of_deps :
  Prims.string Prims.list ->
    FStar_JsonHelper.repl_task Prims.list ->
      FStar_JsonHelper.repl_task Prims.list)
  =
  fun deps ->
    fun final_tasks ->
      let wrap fname =
        let uu____104 = FStar_Util.now () in
        {
          FStar_JsonHelper.tf_fname = fname;
          FStar_JsonHelper.tf_modtime = uu____104
        } in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____140 =
              let uu____141 =
                let uu____146 = wrap intf in
                let uu____147 = wrap impl in (uu____146, uu____147) in
              FStar_JsonHelper.LDInterleaved uu____141 in
            let uu____148 = aux deps' final_tasks1 in uu____140 :: uu____148
        | intf_or_impl::deps' ->
            let uu____158 =
              let uu____159 = wrap intf_or_impl in
              FStar_JsonHelper.LDSingle uu____159 in
            let uu____160 = aux deps' final_tasks1 in uu____158 :: uu____160
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
      let uu____214 = get_mod_name f in uu____214 = our_mod_name in
    let parse_data_cache = FStar_CheckedFiles.load_parsing_data_from_cache in
    let uu____225 =
      FStar_Dependencies.find_deps_if_needed [filename] parse_data_cache in
    match uu____225 with
    | (deps, dep_graph1) ->
        let uu____254 = FStar_List.partition has_our_mod_name deps in
        (match uu____254 with
         | (same_name, real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____304 =
                       let uu____306 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu____306 in
                     if uu____304
                     then
                       let uu____309 =
                         let uu____315 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.Fatal_MissingInterface, uu____315) in
                       FStar_Errors.raise_err uu____309
                     else ());
                    (let uu____322 =
                       let uu____324 =
                         FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu____324 in
                     if uu____322
                     then
                       let uu____327 =
                         let uu____333 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____333) in
                       FStar_Errors.raise_err uu____327
                     else ());
                    (let uu____339 =
                       let uu____340 =
                         let uu____341 = FStar_Util.now () in
                         {
                           FStar_JsonHelper.tf_fname = intf;
                           FStar_JsonHelper.tf_modtime = uu____341
                         } in
                       FStar_JsonHelper.LDInterfaceOfCurrentFile uu____340 in
                     [uu____339]))
               | impl::[] -> []
               | uu____346 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu____357 =
                       let uu____363 =
                         FStar_Util.format message [our_mod_name; mods_str] in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____363) in
                     FStar_Errors.raise_err uu____357);
                    []) in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
             (real_deps, tasks, dep_graph1))
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      (FStar_JsonHelper.repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun msg ->
      let uu____398 = FStar_TypeChecker_Tc.snapshot_context env msg in
      match uu____398 with
      | (ctx_depth, env1) ->
          let uu____442 = FStar_Options.snapshot () in
          (match uu____442 with
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
          let uu____479 = snapshot_env st.FStar_JsonHelper.repl_env msg in
          match uu____479 with
          | (depth, env) ->
              ((let uu____487 =
                  let uu____488 = FStar_ST.op_Bang repl_stack in
                  (depth, (task, st)) :: uu____488 in
                FStar_ST.op_Colon_Equals repl_stack uu____487);
               (let uu___66_549 = st in
                let uu____550 = set_check_kind env push_kind in
                {
                  FStar_JsonHelper.repl_line =
                    (uu___66_549.FStar_JsonHelper.repl_line);
                  FStar_JsonHelper.repl_column =
                    (uu___66_549.FStar_JsonHelper.repl_column);
                  FStar_JsonHelper.repl_fname =
                    (uu___66_549.FStar_JsonHelper.repl_fname);
                  FStar_JsonHelper.repl_deps_stack =
                    (uu___66_549.FStar_JsonHelper.repl_deps_stack);
                  FStar_JsonHelper.repl_curmod =
                    (uu___66_549.FStar_JsonHelper.repl_curmod);
                  FStar_JsonHelper.repl_env = uu____550;
                  FStar_JsonHelper.repl_stdin =
                    (uu___66_549.FStar_JsonHelper.repl_stdin);
                  FStar_JsonHelper.repl_names =
                    (uu___66_549.FStar_JsonHelper.repl_names)
                }))
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver1 ->
    fun msg ->
      fun uu____583 ->
        match uu____583 with
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
      let uu____654 = FStar_ST.op_Bang repl_stack in
      match uu____654 with
      | [] -> failwith "Too many pops"
      | (depth, (uu____684, st'))::stack_tl ->
          let env =
            rollback_env
              (st.FStar_JsonHelper.repl_env).FStar_TypeChecker_Env.solver msg
              depth in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____731 =
              FStar_Util.physical_equality env st'.FStar_JsonHelper.repl_env in
            FStar_Common.runtime_assert uu____731 "Inconsistent stack state");
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
          let uu____759 =
            let uu____765 = FStar_TypeChecker_Env.dep_graph env in
            FStar_Parser_Dep.parsing_data_of uu____765 in
          FStar_All.pipe_right modf uu____759 in
        let uu____767 =
          FStar_Universal.tc_one_file_for_ide env intf_opt modf parse_data in
        match uu____767 with | (uu____772, env1) -> env1
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
            let uu____800 =
              tc_one env
                (FStar_Pervasives_Native.Some
                   (intf.FStar_JsonHelper.tf_fname))
                impl.FStar_JsonHelper.tf_fname in
            (curmod, uu____800)
        | FStar_JsonHelper.LDSingle intf_or_impl ->
            let uu____803 =
              tc_one env FStar_Pervasives_Native.None
                intf_or_impl.FStar_JsonHelper.tf_fname in
            (curmod, uu____803)
        | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
            let uu____806 =
              FStar_Universal.load_interface_decls env
                intf.FStar_JsonHelper.tf_fname in
            (curmod, uu____806)
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
          (fun uu___114_841 ->
             match () with
             | () ->
                 let uu____847 =
                   run_repl_task st1.FStar_JsonHelper.repl_curmod
                     st1.FStar_JsonHelper.repl_env task in
                 (match uu____847 with
                  | (curmod, env) ->
                      let st2 =
                        let uu___139_860 = st1 in
                        {
                          FStar_JsonHelper.repl_line =
                            (uu___139_860.FStar_JsonHelper.repl_line);
                          FStar_JsonHelper.repl_column =
                            (uu___139_860.FStar_JsonHelper.repl_column);
                          FStar_JsonHelper.repl_fname =
                            (uu___139_860.FStar_JsonHelper.repl_fname);
                          FStar_JsonHelper.repl_deps_stack =
                            (uu___139_860.FStar_JsonHelper.repl_deps_stack);
                          FStar_JsonHelper.repl_curmod = curmod;
                          FStar_JsonHelper.repl_env = env;
                          FStar_JsonHelper.repl_stdin =
                            (uu___139_860.FStar_JsonHelper.repl_stdin);
                          FStar_JsonHelper.repl_names =
                            (uu___139_860.FStar_JsonHelper.repl_names)
                        } in
                      (true, st2))) ()
        with
        | FStar_All.Failure msg ->
            (FStar_Util.print1_error "[F] %s" msg;
             (let uu____877 = pop_repl "run_tx" st1 in (false, uu____877)))
        | FStar_Util.SigInt ->
            (FStar_Util.print_error "[E] Interrupt";
             (let uu____883 = pop_repl "run_tx" st1 in (false, uu____883)))
        | FStar_Errors.Error (e, msg, r) ->
            (FStar_Util.print1_error "[E] %s" msg;
             (let uu____894 = pop_repl "run_tx" st1 in (false, uu____894)))
        | FStar_Errors.Err (e, msg) ->
            (FStar_Util.print1_error "[E] %s" msg;
             (let uu____904 = pop_repl "run_tx" st1 in (false, uu____904)))
        | FStar_Errors.Stop ->
            (FStar_Util.print_error "[E] Stop";
             (let uu____910 = pop_repl "run_tx" st1 in (false, uu____910)))
let (tf_of_fname : Prims.string -> FStar_JsonHelper.timed_fname) =
  fun fname ->
    let uu____922 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname in
    {
      FStar_JsonHelper.tf_fname = fname;
      FStar_JsonHelper.tf_modtime = uu____922
    }
let (update_task_timestamps :
  FStar_JsonHelper.repl_task -> FStar_JsonHelper.repl_task) =
  fun uu___0_928 ->
    match uu___0_928 with
    | FStar_JsonHelper.LDInterleaved (intf, impl) ->
        let uu____931 =
          let uu____936 = tf_of_fname intf.FStar_JsonHelper.tf_fname in
          let uu____937 = tf_of_fname impl.FStar_JsonHelper.tf_fname in
          (uu____936, uu____937) in
        FStar_JsonHelper.LDInterleaved uu____931
    | FStar_JsonHelper.LDSingle intf_or_impl ->
        let uu____939 = tf_of_fname intf_or_impl.FStar_JsonHelper.tf_fname in
        FStar_JsonHelper.LDSingle uu____939
    | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu____941 = tf_of_fname intf.FStar_JsonHelper.tf_fname in
        FStar_JsonHelper.LDInterfaceOfCurrentFile uu____941
    | other -> other
let (repl_ldtx :
  FStar_JsonHelper.repl_state ->
    FStar_JsonHelper.repl_task Prims.list -> either_replst)
  =
  fun st ->
    fun tasks ->
      let rec revert_many st1 uu___1_978 =
        match uu___1_978 with
        | [] -> st1
        | (_id, (task, _st'))::entries ->
            let st' = pop_repl "repl_ldtx" st1 in
            let dep_graph1 =
              FStar_TypeChecker_Env.dep_graph st1.FStar_JsonHelper.repl_env in
            let st'1 =
              let uu___168_1027 = st' in
              let uu____1028 =
                FStar_TypeChecker_Env.set_dep_graph
                  st'.FStar_JsonHelper.repl_env dep_graph1 in
              {
                FStar_JsonHelper.repl_line =
                  (uu___168_1027.FStar_JsonHelper.repl_line);
                FStar_JsonHelper.repl_column =
                  (uu___168_1027.FStar_JsonHelper.repl_column);
                FStar_JsonHelper.repl_fname =
                  (uu___168_1027.FStar_JsonHelper.repl_fname);
                FStar_JsonHelper.repl_deps_stack =
                  (uu___168_1027.FStar_JsonHelper.repl_deps_stack);
                FStar_JsonHelper.repl_curmod =
                  (uu___168_1027.FStar_JsonHelper.repl_curmod);
                FStar_JsonHelper.repl_env = uu____1028;
                FStar_JsonHelper.repl_stdin =
                  (uu___168_1027.FStar_JsonHelper.repl_stdin);
                FStar_JsonHelper.repl_names =
                  (uu___168_1027.FStar_JsonHelper.repl_names)
              } in
            revert_many st'1 entries in
      let rec aux st1 tasks1 previous =
        match (tasks1, previous) with
        | ([], []) -> FStar_Util.Inl st1
        | (task::tasks2, []) ->
            let timestamped_task = update_task_timestamps task in
            let uu____1078 = repl_tx st1 LaxCheck timestamped_task in
            (match uu____1078 with
             | (success, st2) ->
                 if success
                 then
                   let uu____1097 =
                     let uu___188_1098 = st2 in
                     let uu____1099 = FStar_ST.op_Bang repl_stack in
                     {
                       FStar_JsonHelper.repl_line =
                         (uu___188_1098.FStar_JsonHelper.repl_line);
                       FStar_JsonHelper.repl_column =
                         (uu___188_1098.FStar_JsonHelper.repl_column);
                       FStar_JsonHelper.repl_fname =
                         (uu___188_1098.FStar_JsonHelper.repl_fname);
                       FStar_JsonHelper.repl_deps_stack = uu____1099;
                       FStar_JsonHelper.repl_curmod =
                         (uu___188_1098.FStar_JsonHelper.repl_curmod);
                       FStar_JsonHelper.repl_env =
                         (uu___188_1098.FStar_JsonHelper.repl_env);
                       FStar_JsonHelper.repl_stdin =
                         (uu___188_1098.FStar_JsonHelper.repl_stdin);
                       FStar_JsonHelper.repl_names =
                         (uu___188_1098.FStar_JsonHelper.repl_names)
                     } in
                   aux uu____1097 tasks2 []
                 else FStar_Util.Inr st2)
        | (task::tasks2, prev::previous1) when
            let uu____1143 = update_task_timestamps task in
            (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
              = uu____1143
            -> aux st1 tasks2 previous1
        | (tasks2, previous1) ->
            let uu____1158 = revert_many st1 previous1 in
            aux uu____1158 tasks2 [] in
      aux st tasks (FStar_List.rev st.FStar_JsonHelper.repl_deps_stack)
let (ld_deps :
  FStar_JsonHelper.repl_state ->
    ((FStar_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    try
      (fun uu___202_1203 ->
         match () with
         | () ->
             let uu____1215 =
               deps_and_repl_ld_tasks_of_our_file
                 st.FStar_JsonHelper.repl_fname in
             (match uu____1215 with
              | (deps, tasks, dep_graph1) ->
                  let st1 =
                    let uu___212_1252 = st in
                    let uu____1253 =
                      FStar_TypeChecker_Env.set_dep_graph
                        st.FStar_JsonHelper.repl_env dep_graph1 in
                    {
                      FStar_JsonHelper.repl_line =
                        (uu___212_1252.FStar_JsonHelper.repl_line);
                      FStar_JsonHelper.repl_column =
                        (uu___212_1252.FStar_JsonHelper.repl_column);
                      FStar_JsonHelper.repl_fname =
                        (uu___212_1252.FStar_JsonHelper.repl_fname);
                      FStar_JsonHelper.repl_deps_stack =
                        (uu___212_1252.FStar_JsonHelper.repl_deps_stack);
                      FStar_JsonHelper.repl_curmod =
                        (uu___212_1252.FStar_JsonHelper.repl_curmod);
                      FStar_JsonHelper.repl_env = uu____1253;
                      FStar_JsonHelper.repl_stdin =
                        (uu___212_1252.FStar_JsonHelper.repl_stdin);
                      FStar_JsonHelper.repl_names =
                        (uu___212_1252.FStar_JsonHelper.repl_names)
                    } in
                  let uu____1254 = repl_ldtx st1 tasks in
                  (match uu____1254 with
                   | FStar_Util.Inr st2 -> FStar_Util.Inr st2
                   | FStar_Util.Inl st2 -> FStar_Util.Inl (st2, deps)))) ()
    with
    | uu___201_1287 ->
        (FStar_Util.print_error "[E] Failed to load deps"; FStar_Util.Inr st)
let (add_module_completions :
  Prims.string ->
    Prims.string Prims.list ->
      FStar_Interactive_CompletionTable.table ->
        FStar_Interactive_CompletionTable.table)
  =
  fun this_fname ->
    fun deps ->
      fun table ->
        let capitalize str =
          if str = ""
          then str
          else
            (let first =
               FStar_String.substring str (Prims.parse_int "0")
                 (Prims.parse_int "1") in
             let uu____1351 =
               FStar_String.substring str (Prims.parse_int "1")
                 ((FStar_String.length str) - (Prims.parse_int "1")) in
             Prims.op_Hat (FStar_String.uppercase first) uu____1351) in
        let mods = FStar_Parser_Dep.build_inclusion_candidates_list () in
        let loaded_mods_set =
          let uu____1368 = FStar_Util.psmap_empty () in
          let uu____1373 =
            let uu____1377 = FStar_Options.prims () in uu____1377 :: deps in
          FStar_List.fold_left
            (fun acc ->
               fun dep1 ->
                 let uu____1393 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____1393 true) uu____1368
            uu____1373 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1 ->
             fun uu____1422 ->
               match uu____1422 with
               | (modname, mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____1445 = capitalize modname in
                        FStar_Util.split uu____1445 "." in
                      let uu____1448 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____1448 mod_path ns_query)) table
          (FStar_List.rev mods)
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
      let uu____1472 = ld_deps st in
      match uu____1472 with
      | FStar_Util.Inl (st1, deps) ->
          let names1 =
            add_module_completions st1.FStar_JsonHelper.repl_fname deps
              st1.FStar_JsonHelper.repl_names in
          let uu____1500 =
            repl_tx
              (let uu___248_1508 = st1 in
               {
                 FStar_JsonHelper.repl_line =
                   (uu___248_1508.FStar_JsonHelper.repl_line);
                 FStar_JsonHelper.repl_column =
                   (uu___248_1508.FStar_JsonHelper.repl_column);
                 FStar_JsonHelper.repl_fname =
                   (uu___248_1508.FStar_JsonHelper.repl_fname);
                 FStar_JsonHelper.repl_deps_stack =
                   (uu___248_1508.FStar_JsonHelper.repl_deps_stack);
                 FStar_JsonHelper.repl_curmod =
                   (uu___248_1508.FStar_JsonHelper.repl_curmod);
                 FStar_JsonHelper.repl_env =
                   (uu___248_1508.FStar_JsonHelper.repl_env);
                 FStar_JsonHelper.repl_stdin =
                   (uu___248_1508.FStar_JsonHelper.repl_stdin);
                 FStar_JsonHelper.repl_names = names1
               }) LaxCheck (FStar_JsonHelper.PushFragment frag) in
          FStar_Pervasives_Native.snd uu____1500
      | FStar_Util.Inr st1 -> st1