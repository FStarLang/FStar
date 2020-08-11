open Prims
type push_kind =
  | SyntaxCheck 
  | LaxCheck 
  | FullCheck 
let (uu___is_SyntaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | SyntaxCheck -> true | uu____5 -> false
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | LaxCheck -> true | uu____11 -> false
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | FullCheck -> true | uu____17 -> false
type ctx_depth_t =
  (Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t * Prims.int)
type deps_t = FStar_Parser_Dep.deps
type either_replst =
  (FStar_Interactive_JsonHelper.repl_state,
    FStar_Interactive_JsonHelper.repl_state) FStar_Util.either
let (repl_stack : FStar_Interactive_JsonHelper.repl_stack_t FStar_ST.ref) =
  FStar_Util.mk_ref []
let (set_check_kind :
  FStar_TypeChecker_Env.env_t -> push_kind -> FStar_TypeChecker_Env.env_t) =
  fun env ->
    fun check_kind ->
      let uu___4_52 = env in
      let uu____53 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___4_52.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range = (uu___4_52.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___4_52.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma = (uu___4_52.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___4_52.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___4_52.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___4_52.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___4_52.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___4_52.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___4_52.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___4_52.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___4_52.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___4_52.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___4_52.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___4_52.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___4_52.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___4_52.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___4_52.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___4_52.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (uu___4_52.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___4_52.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___4_52.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___4_52.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___4_52.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___4_52.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___4_52.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___4_52.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___4_52.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___4_52.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___4_52.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___4_52.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___4_52.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___4_52.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___4_52.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___4_52.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.try_solve_implicits_hook =
          (uu___4_52.FStar_TypeChecker_Env.try_solve_implicits_hook);
        FStar_TypeChecker_Env.splice =
          (uu___4_52.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.mpreprocess =
          (uu___4_52.FStar_TypeChecker_Env.mpreprocess);
        FStar_TypeChecker_Env.postprocess =
          (uu___4_52.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.identifier_info =
          (uu___4_52.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___4_52.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____53;
        FStar_TypeChecker_Env.nbe = (uu___4_52.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___4_52.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___4_52.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___4_52.FStar_TypeChecker_Env.enable_defer_to_tac)
      }
let (repl_ld_tasks_of_deps :
  Prims.string Prims.list ->
    FStar_Interactive_JsonHelper.repl_task Prims.list ->
      FStar_Interactive_JsonHelper.repl_task Prims.list)
  =
  fun deps ->
    fun final_tasks ->
      let wrap fname =
        let uu____80 = FStar_Util.now () in
        {
          FStar_Interactive_JsonHelper.tf_fname = fname;
          FStar_Interactive_JsonHelper.tf_modtime = uu____80
        } in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____109 =
              let uu____110 =
                let uu____115 = wrap intf in
                let uu____116 = wrap impl in (uu____115, uu____116) in
              FStar_Interactive_JsonHelper.LDInterleaved uu____110 in
            let uu____117 = aux deps' final_tasks1 in uu____109 :: uu____117
        | intf_or_impl::deps' ->
            let uu____124 =
              let uu____125 = wrap intf_or_impl in
              FStar_Interactive_JsonHelper.LDSingle uu____125 in
            let uu____126 = aux deps' final_tasks1 in uu____124 :: uu____126
        | [] -> final_tasks1 in
      aux deps final_tasks
let (deps_and_repl_ld_tasks_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * FStar_Interactive_JsonHelper.repl_task
      Prims.list * deps_t))
  =
  fun filename ->
    let get_mod_name fname = FStar_Parser_Dep.lowercase_module_name fname in
    let our_mod_name = get_mod_name filename in
    let has_our_mod_name f =
      let uu____167 = get_mod_name f in uu____167 = our_mod_name in
    let parse_data_cache = FStar_CheckedFiles.load_parsing_data_from_cache in
    let uu____175 =
      FStar_Dependencies.find_deps_if_needed [filename] parse_data_cache in
    match uu____175 with
    | (deps, dep_graph) ->
        let uu____198 = FStar_List.partition has_our_mod_name deps in
        (match uu____198 with
         | (same_name, real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____235 =
                       let uu____236 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu____236 in
                     if uu____235
                     then
                       let uu____237 =
                         let uu____242 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.Fatal_MissingInterface, uu____242) in
                       FStar_Errors.raise_err uu____237
                     else ());
                    (let uu____245 =
                       let uu____246 =
                         FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu____246 in
                     if uu____245
                     then
                       let uu____247 =
                         let uu____252 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____252) in
                       FStar_Errors.raise_err uu____247
                     else ());
                    (let uu____254 =
                       let uu____255 =
                         let uu____256 = FStar_Util.now () in
                         {
                           FStar_Interactive_JsonHelper.tf_fname = intf;
                           FStar_Interactive_JsonHelper.tf_modtime =
                             uu____256
                         } in
                       FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile
                         uu____255 in
                     [uu____254]))
               | impl::[] -> []
               | uu____258 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu____264 =
                       let uu____269 =
                         FStar_Util.format message [our_mod_name; mods_str] in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____269) in
                     FStar_Errors.raise_err uu____264);
                    []) in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
             (real_deps, tasks, dep_graph))
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      (FStar_Interactive_JsonHelper.repl_depth_t *
        FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun msg ->
      let uu____295 = FStar_TypeChecker_Tc.snapshot_context env msg in
      match uu____295 with
      | (ctx_depth, env1) ->
          let uu____330 = FStar_Options.snapshot () in
          (match uu____330 with
           | (opt_depth, ()) -> ((ctx_depth, opt_depth), env1))
let (push_repl :
  Prims.string ->
    push_kind ->
      FStar_Interactive_JsonHelper.repl_task ->
        FStar_Interactive_JsonHelper.repl_state ->
          FStar_Interactive_JsonHelper.repl_state)
  =
  fun msg ->
    fun push_kind1 ->
      fun task ->
        fun st ->
          let uu____360 =
            snapshot_env st.FStar_Interactive_JsonHelper.repl_env msg in
          match uu____360 with
          | (depth, env) ->
              ((let uu____368 =
                  let uu____369 = FStar_ST.op_Bang repl_stack in
                  (depth, (task, st)) :: uu____369 in
                FStar_ST.op_Colon_Equals repl_stack uu____368);
               (let uu___66_404 = st in
                let uu____405 = set_check_kind env push_kind1 in
                {
                  FStar_Interactive_JsonHelper.repl_line =
                    (uu___66_404.FStar_Interactive_JsonHelper.repl_line);
                  FStar_Interactive_JsonHelper.repl_column =
                    (uu___66_404.FStar_Interactive_JsonHelper.repl_column);
                  FStar_Interactive_JsonHelper.repl_fname =
                    (uu___66_404.FStar_Interactive_JsonHelper.repl_fname);
                  FStar_Interactive_JsonHelper.repl_deps_stack =
                    (uu___66_404.FStar_Interactive_JsonHelper.repl_deps_stack);
                  FStar_Interactive_JsonHelper.repl_curmod =
                    (uu___66_404.FStar_Interactive_JsonHelper.repl_curmod);
                  FStar_Interactive_JsonHelper.repl_env = uu____405;
                  FStar_Interactive_JsonHelper.repl_stdin =
                    (uu___66_404.FStar_Interactive_JsonHelper.repl_stdin);
                  FStar_Interactive_JsonHelper.repl_names =
                    (uu___66_404.FStar_Interactive_JsonHelper.repl_names)
                }))
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver ->
    fun msg ->
      fun uu____432 ->
        match uu____432 with
        | (ctx_depth, opt_depth) ->
            let env =
              FStar_TypeChecker_Tc.rollback_context solver msg
                (FStar_Pervasives_Native.Some ctx_depth) in
            (FStar_Options.rollback (FStar_Pervasives_Native.Some opt_depth);
             env)
let (pop_repl :
  Prims.string ->
    FStar_Interactive_JsonHelper.repl_state ->
      FStar_Interactive_JsonHelper.repl_state)
  =
  fun msg ->
    fun st ->
      let uu____483 = FStar_ST.op_Bang repl_stack in
      match uu____483 with
      | [] -> failwith "Too many pops"
      | (depth, (uu____499, st'))::stack_tl ->
          let env =
            rollback_env
              (st.FStar_Interactive_JsonHelper.repl_env).FStar_TypeChecker_Env.solver
              msg depth in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____533 =
              FStar_Util.physical_equality env
                st'.FStar_Interactive_JsonHelper.repl_env in
            FStar_Common.runtime_assert uu____533 "Inconsistent stack state");
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
          let uu____554 =
            let uu____559 = FStar_TypeChecker_Env.dep_graph env in
            FStar_Parser_Dep.parsing_data_of uu____559 in
          FStar_All.pipe_right modf uu____554 in
        let uu____560 =
          FStar_Universal.tc_one_file_for_ide env intf_opt modf parse_data in
        match uu____560 with | (uu____565, env1) -> env1
let (run_repl_task :
  FStar_Interactive_JsonHelper.optmod_t ->
    FStar_TypeChecker_Env.env_t ->
      FStar_Interactive_JsonHelper.repl_task ->
        (FStar_Interactive_JsonHelper.optmod_t * FStar_TypeChecker_Env.env_t))
  =
  fun curmod ->
    fun env ->
      fun task ->
        match task with
        | FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) ->
            let uu____592 =
              tc_one env
                (FStar_Pervasives_Native.Some
                   (intf.FStar_Interactive_JsonHelper.tf_fname))
                impl.FStar_Interactive_JsonHelper.tf_fname in
            (curmod, uu____592)
        | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
            let uu____594 =
              tc_one env FStar_Pervasives_Native.None
                intf_or_impl.FStar_Interactive_JsonHelper.tf_fname in
            (curmod, uu____594)
        | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
            let uu____596 =
              FStar_Universal.load_interface_decls env
                intf.FStar_Interactive_JsonHelper.tf_fname in
            (curmod, uu____596)
        | FStar_Interactive_JsonHelper.PushFragment frag ->
            FStar_Universal.tc_one_fragment curmod env frag
        | FStar_Interactive_JsonHelper.Noop -> (curmod, env)
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of (FStar_Syntax_Syntax.binding,
  FStar_TypeChecker_Env.sig_binding) FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTAlias _0 -> true | uu____648 -> false
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee -> match projectee with | NTAlias _0 -> _0
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTOpen _0 -> true | uu____683 -> false
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee -> match projectee with | NTOpen _0 -> _0
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTInclude _0 -> true | uu____712 -> false
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee -> match projectee with | NTInclude _0 -> _0
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTBinding _0 -> true | uu____741 -> false
let (__proj__NTBinding__item___0 :
  name_tracking_event ->
    (FStar_Syntax_Syntax.binding, FStar_TypeChecker_Env.sig_binding)
      FStar_Util.either)
  = fun projectee -> match projectee with | NTBinding _0 -> _0
let (query_of_ids :
  FStar_Ident.ident Prims.list -> FStar_Interactive_CompletionTable.query) =
  fun ids -> FStar_List.map FStar_Ident.string_of_id ids
let (query_of_lid :
  FStar_Ident.lident -> FStar_Interactive_CompletionTable.query) =
  fun lid ->
    let uu____774 =
      let uu____777 = FStar_Ident.ns_of_lid lid in
      let uu____780 =
        let uu____783 = FStar_Ident.ident_of_lid lid in [uu____783] in
      FStar_List.append uu____777 uu____780 in
    query_of_ids uu____774
let (update_names_from_event :
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod_str ->
    fun table ->
      fun evt ->
        let is_cur_mod lid =
          let uu____805 = FStar_Ident.string_of_lid lid in
          uu____805 = cur_mod_str in
        match evt with
        | NTAlias (host, id, included) ->
            let uu____809 = is_cur_mod host in
            if uu____809
            then
              let uu____810 = FStar_Ident.string_of_id id in
              let uu____811 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                uu____810 [] uu____811
            else table
        | NTOpen (host, (included, kind)) ->
            let uu____816 = is_cur_mod host in
            if uu____816
            then
              let uu____817 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____817
            else table
        | NTInclude (host, included) ->
            let uu____821 =
              let uu____822 = is_cur_mod host in
              if uu____822 then [] else query_of_lid host in
            let uu____824 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____821 uu____824
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid, uu____836)) -> [lid]
              | FStar_Util.Inr (lids, uu____850) -> lids
              | uu____855 -> [] in
            FStar_List.fold_left
              (fun tbl ->
                 fun lid ->
                   let ns_query =
                     let uu____867 =
                       let uu____868 = FStar_Ident.nsstr lid in
                       uu____868 = cur_mod_str in
                     if uu____867
                     then []
                     else
                       (let uu____870 = FStar_Ident.ns_of_lid lid in
                        query_of_ids uu____870) in
                   let uu____873 =
                     let uu____874 = FStar_Ident.ident_of_lid lid in
                     FStar_Ident.string_of_id uu____874 in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____873 lid) table lids
let (commit_name_tracking' :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event Prims.list ->
        FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod ->
    fun names ->
      fun name_events ->
        let cur_mod_str =
          match cur_mod with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some md ->
              let uu____900 = FStar_Syntax_Syntax.mod_name md in
              FStar_Ident.string_of_lid uu____900 in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names name_events
let (commit_name_tracking :
  FStar_Interactive_JsonHelper.repl_state ->
    name_tracking_event Prims.list -> FStar_Interactive_JsonHelper.repl_state)
  =
  fun st ->
    fun name_events ->
      let names =
        commit_name_tracking' st.FStar_Interactive_JsonHelper.repl_curmod
          st.FStar_Interactive_JsonHelper.repl_names name_events in
      let uu___166_925 = st in
      {
        FStar_Interactive_JsonHelper.repl_line =
          (uu___166_925.FStar_Interactive_JsonHelper.repl_line);
        FStar_Interactive_JsonHelper.repl_column =
          (uu___166_925.FStar_Interactive_JsonHelper.repl_column);
        FStar_Interactive_JsonHelper.repl_fname =
          (uu___166_925.FStar_Interactive_JsonHelper.repl_fname);
        FStar_Interactive_JsonHelper.repl_deps_stack =
          (uu___166_925.FStar_Interactive_JsonHelper.repl_deps_stack);
        FStar_Interactive_JsonHelper.repl_curmod =
          (uu___166_925.FStar_Interactive_JsonHelper.repl_curmod);
        FStar_Interactive_JsonHelper.repl_env =
          (uu___166_925.FStar_Interactive_JsonHelper.repl_env);
        FStar_Interactive_JsonHelper.repl_stdin =
          (uu___166_925.FStar_Interactive_JsonHelper.repl_stdin);
        FStar_Interactive_JsonHelper.repl_names = names
      }
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____940 ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____954 =
        let uu____957 = FStar_ST.op_Bang events in evt :: uu____957 in
      FStar_ST.op_Colon_Equals events uu____954 in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv ->
             fun op ->
               let uu____992 =
                 let uu____993 =
                   let uu____998 = FStar_Syntax_DsEnv.current_module dsenv in
                   (uu____998, op) in
                 NTOpen uu____993 in
               push_event uu____992);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv ->
             fun ns ->
               let uu____1004 =
                 let uu____1005 =
                   let uu____1010 = FStar_Syntax_DsEnv.current_module dsenv in
                   (uu____1010, ns) in
                 NTInclude uu____1005 in
               push_event uu____1004);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv ->
             fun x ->
               fun l ->
                 let uu____1018 =
                   let uu____1019 =
                     let uu____1026 = FStar_Syntax_DsEnv.current_module dsenv in
                     (uu____1026, x, l) in
                   NTAlias uu____1019 in
                 push_event uu____1018)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1031 -> fun s -> push_event (NTBinding s))
      })
let (track_name_changes :
  FStar_TypeChecker_Env.env_t ->
    (FStar_TypeChecker_Env.env_t *
      (FStar_TypeChecker_Env.env_t ->
         (FStar_TypeChecker_Env.env_t * name_tracking_event Prims.list))))
  =
  fun env ->
    let set_hooks dshooks tchooks env1 =
      let uu____1084 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv ->
             let uu____1092 = FStar_Syntax_DsEnv.set_ds_hooks dsenv dshooks in
             ((), uu____1092)) in
      match uu____1084 with
      | ((), tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu____1094 =
      let uu____1099 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu____1100 = FStar_TypeChecker_Env.tc_hooks env in
      (uu____1099, uu____1100) in
    match uu____1094 with
    | (old_dshooks, old_tchooks) ->
        let uu____1116 = fresh_name_tracking_hooks () in
        (match uu____1116 with
         | (events, new_dshooks, new_tchooks) ->
             let uu____1151 = set_hooks new_dshooks new_tchooks env in
             (uu____1151,
               ((fun env1 ->
                   let uu____1165 = set_hooks old_dshooks old_tchooks env1 in
                   let uu____1166 =
                     let uu____1169 = FStar_ST.op_Bang events in
                     FStar_List.rev uu____1169 in
                   (uu____1165, uu____1166)))))
let (repl_tx :
  FStar_Interactive_JsonHelper.repl_state ->
    push_kind ->
      FStar_Interactive_JsonHelper.repl_task ->
        (FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option *
          FStar_Interactive_JsonHelper.repl_state))
  =
  fun st ->
    fun push_kind1 ->
      fun task ->
        try
          (fun uu___202_1224 ->
             match () with
             | () ->
                 let st1 = push_repl "repl_tx" push_kind1 task st in
                 let uu____1232 =
                   track_name_changes
                     st1.FStar_Interactive_JsonHelper.repl_env in
                 (match uu____1232 with
                  | (env, finish_name_tracking) ->
                      let uu____1272 =
                        run_repl_task
                          st1.FStar_Interactive_JsonHelper.repl_curmod env
                          task in
                      (match uu____1272 with
                       | (curmod, env1) ->
                           let st2 =
                             let uu___228_1286 = st1 in
                             {
                               FStar_Interactive_JsonHelper.repl_line =
                                 (uu___228_1286.FStar_Interactive_JsonHelper.repl_line);
                               FStar_Interactive_JsonHelper.repl_column =
                                 (uu___228_1286.FStar_Interactive_JsonHelper.repl_column);
                               FStar_Interactive_JsonHelper.repl_fname =
                                 (uu___228_1286.FStar_Interactive_JsonHelper.repl_fname);
                               FStar_Interactive_JsonHelper.repl_deps_stack =
                                 (uu___228_1286.FStar_Interactive_JsonHelper.repl_deps_stack);
                               FStar_Interactive_JsonHelper.repl_curmod =
                                 curmod;
                               FStar_Interactive_JsonHelper.repl_env = env1;
                               FStar_Interactive_JsonHelper.repl_stdin =
                                 (uu___228_1286.FStar_Interactive_JsonHelper.repl_stdin);
                               FStar_Interactive_JsonHelper.repl_names =
                                 (uu___228_1286.FStar_Interactive_JsonHelper.repl_names)
                             } in
                           let uu____1287 = finish_name_tracking env1 in
                           (match uu____1287 with
                            | (env2, name_events) ->
                                let uu____1306 =
                                  commit_name_tracking st2 name_events in
                                (FStar_Pervasives_Native.None, uu____1306)))))
            ()
        with
        | FStar_All.Failure msg ->
            let uu____1320 =
              let uu____1323 =
                FStar_Interactive_JsonHelper.js_diag
                  st.FStar_Interactive_JsonHelper.repl_fname msg
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____1323 in
            (uu____1320, st)
        | FStar_Util.SigInt ->
            (FStar_Util.print_error "[E] Interrupt";
             (FStar_Pervasives_Native.None, st))
        | FStar_Errors.Error (e, msg, r) ->
            let uu____1332 =
              let uu____1335 =
                FStar_Interactive_JsonHelper.js_diag
                  st.FStar_Interactive_JsonHelper.repl_fname msg
                  (FStar_Pervasives_Native.Some r) in
              FStar_Pervasives_Native.Some uu____1335 in
            (uu____1332, st)
        | FStar_Errors.Err (e, msg) ->
            let uu____1340 =
              let uu____1343 =
                FStar_Interactive_JsonHelper.js_diag
                  st.FStar_Interactive_JsonHelper.repl_fname msg
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu____1343 in
            (uu____1340, st)
        | FStar_Errors.Stop ->
            (FStar_Util.print_error "[E] Stop";
             (FStar_Pervasives_Native.None, st))
let (tf_of_fname : Prims.string -> FStar_Interactive_JsonHelper.timed_fname)
  =
  fun fname ->
    let uu____1354 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname in
    {
      FStar_Interactive_JsonHelper.tf_fname = fname;
      FStar_Interactive_JsonHelper.tf_modtime = uu____1354
    }
let (update_task_timestamps :
  FStar_Interactive_JsonHelper.repl_task ->
    FStar_Interactive_JsonHelper.repl_task)
  =
  fun uu___0_1359 ->
    match uu___0_1359 with
    | FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) ->
        let uu____1362 =
          let uu____1367 =
            tf_of_fname intf.FStar_Interactive_JsonHelper.tf_fname in
          let uu____1368 =
            tf_of_fname impl.FStar_Interactive_JsonHelper.tf_fname in
          (uu____1367, uu____1368) in
        FStar_Interactive_JsonHelper.LDInterleaved uu____1362
    | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
        let uu____1370 =
          tf_of_fname intf_or_impl.FStar_Interactive_JsonHelper.tf_fname in
        FStar_Interactive_JsonHelper.LDSingle uu____1370
    | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu____1372 =
          tf_of_fname intf.FStar_Interactive_JsonHelper.tf_fname in
        FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile uu____1372
    | other -> other
let (repl_ldtx :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Interactive_JsonHelper.repl_task Prims.list -> either_replst)
  =
  fun st ->
    fun tasks ->
      let rec revert_many st1 uu___1_1408 =
        match uu___1_1408 with
        | [] -> st1
        | (_id, (task, _st'))::entries ->
            let st' = pop_repl "repl_ldtx" st1 in
            let dep_graph =
              FStar_TypeChecker_Env.dep_graph
                st1.FStar_Interactive_JsonHelper.repl_env in
            let st'1 =
              let uu___260_1456 = st' in
              let uu____1457 =
                FStar_TypeChecker_Env.set_dep_graph
                  st'.FStar_Interactive_JsonHelper.repl_env dep_graph in
              {
                FStar_Interactive_JsonHelper.repl_line =
                  (uu___260_1456.FStar_Interactive_JsonHelper.repl_line);
                FStar_Interactive_JsonHelper.repl_column =
                  (uu___260_1456.FStar_Interactive_JsonHelper.repl_column);
                FStar_Interactive_JsonHelper.repl_fname =
                  (uu___260_1456.FStar_Interactive_JsonHelper.repl_fname);
                FStar_Interactive_JsonHelper.repl_deps_stack =
                  (uu___260_1456.FStar_Interactive_JsonHelper.repl_deps_stack);
                FStar_Interactive_JsonHelper.repl_curmod =
                  (uu___260_1456.FStar_Interactive_JsonHelper.repl_curmod);
                FStar_Interactive_JsonHelper.repl_env = uu____1457;
                FStar_Interactive_JsonHelper.repl_stdin =
                  (uu___260_1456.FStar_Interactive_JsonHelper.repl_stdin);
                FStar_Interactive_JsonHelper.repl_names =
                  (uu___260_1456.FStar_Interactive_JsonHelper.repl_names)
              } in
            revert_many st'1 entries in
      let rec aux st1 tasks1 previous =
        match (tasks1, previous) with
        | ([], []) -> FStar_Util.Inl st1
        | (task::tasks2, []) ->
            let timestamped_task = update_task_timestamps task in
            let uu____1507 = repl_tx st1 LaxCheck timestamped_task in
            (match uu____1507 with
             | (diag, st2) ->
                 if Prims.op_Negation (FStar_Util.is_some diag)
                 then
                   let uu____1528 =
                     let uu___280_1529 = st2 in
                     let uu____1530 = FStar_ST.op_Bang repl_stack in
                     {
                       FStar_Interactive_JsonHelper.repl_line =
                         (uu___280_1529.FStar_Interactive_JsonHelper.repl_line);
                       FStar_Interactive_JsonHelper.repl_column =
                         (uu___280_1529.FStar_Interactive_JsonHelper.repl_column);
                       FStar_Interactive_JsonHelper.repl_fname =
                         (uu___280_1529.FStar_Interactive_JsonHelper.repl_fname);
                       FStar_Interactive_JsonHelper.repl_deps_stack =
                         uu____1530;
                       FStar_Interactive_JsonHelper.repl_curmod =
                         (uu___280_1529.FStar_Interactive_JsonHelper.repl_curmod);
                       FStar_Interactive_JsonHelper.repl_env =
                         (uu___280_1529.FStar_Interactive_JsonHelper.repl_env);
                       FStar_Interactive_JsonHelper.repl_stdin =
                         (uu___280_1529.FStar_Interactive_JsonHelper.repl_stdin);
                       FStar_Interactive_JsonHelper.repl_names =
                         (uu___280_1529.FStar_Interactive_JsonHelper.repl_names)
                     } in
                   aux uu____1528 tasks2 []
                 else FStar_Util.Inr st2)
        | (task::tasks2, prev::previous1) when
            let uu____1560 = update_task_timestamps task in
            (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
              = uu____1560
            -> aux st1 tasks2 previous1
        | (tasks2, previous1) ->
            let uu____1575 = revert_many st1 previous1 in
            aux uu____1575 tasks2 [] in
      aux st tasks
        (FStar_List.rev st.FStar_Interactive_JsonHelper.repl_deps_stack)
let (ld_deps :
  FStar_Interactive_JsonHelper.repl_state ->
    ((FStar_Interactive_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_Interactive_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    try
      (fun uu___294_1617 ->
         match () with
         | () ->
             let uu____1628 =
               deps_and_repl_ld_tasks_of_our_file
                 st.FStar_Interactive_JsonHelper.repl_fname in
             (match uu____1628 with
              | (deps, tasks, dep_graph) ->
                  let st1 =
                    let uu___304_1661 = st in
                    let uu____1662 =
                      FStar_TypeChecker_Env.set_dep_graph
                        st.FStar_Interactive_JsonHelper.repl_env dep_graph in
                    {
                      FStar_Interactive_JsonHelper.repl_line =
                        (uu___304_1661.FStar_Interactive_JsonHelper.repl_line);
                      FStar_Interactive_JsonHelper.repl_column =
                        (uu___304_1661.FStar_Interactive_JsonHelper.repl_column);
                      FStar_Interactive_JsonHelper.repl_fname =
                        (uu___304_1661.FStar_Interactive_JsonHelper.repl_fname);
                      FStar_Interactive_JsonHelper.repl_deps_stack =
                        (uu___304_1661.FStar_Interactive_JsonHelper.repl_deps_stack);
                      FStar_Interactive_JsonHelper.repl_curmod =
                        (uu___304_1661.FStar_Interactive_JsonHelper.repl_curmod);
                      FStar_Interactive_JsonHelper.repl_env = uu____1662;
                      FStar_Interactive_JsonHelper.repl_stdin =
                        (uu___304_1661.FStar_Interactive_JsonHelper.repl_stdin);
                      FStar_Interactive_JsonHelper.repl_names =
                        (uu___304_1661.FStar_Interactive_JsonHelper.repl_names)
                    } in
                  let uu____1663 = repl_ldtx st1 tasks in
                  (match uu____1663 with
                   | FStar_Util.Inr st2 -> FStar_Util.Inr st2
                   | FStar_Util.Inl st2 -> FStar_Util.Inl (st2, deps)))) ()
    with
    | uu___293_1692 ->
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
               FStar_String.substring str Prims.int_zero Prims.int_one in
             let uu____1737 =
               FStar_String.substring str Prims.int_one
                 ((FStar_String.length str) - Prims.int_one) in
             Prims.op_Hat (FStar_String.uppercase first) uu____1737) in
        let mods = FStar_Parser_Dep.build_inclusion_candidates_list () in
        let loaded_mods_set =
          let uu____1748 = FStar_Util.psmap_empty () in
          let uu____1751 =
            let uu____1754 = FStar_Options.prims () in uu____1754 :: deps in
          FStar_List.fold_left
            (fun acc ->
               fun dep ->
                 let uu____1764 = FStar_Parser_Dep.lowercase_module_name dep in
                 FStar_Util.psmap_add acc uu____1764 true) uu____1748
            uu____1751 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1 ->
             fun uu____1782 ->
               match uu____1782 with
               | (modname, mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____1794 = capitalize modname in
                        FStar_Util.split uu____1794 "." in
                      let uu____1795 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____1795 mod_path ns_query)) table
          (FStar_List.rev mods)
let (full_lax :
  Prims.string ->
    FStar_Interactive_JsonHelper.repl_state ->
      (FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option *
        FStar_Interactive_JsonHelper.repl_state))
  =
  fun text ->
    fun st ->
      FStar_TypeChecker_Env.toggle_id_info
        st.FStar_Interactive_JsonHelper.repl_env true;
      (let frag =
         {
           FStar_Parser_ParseIt.frag_fname =
             (st.FStar_Interactive_JsonHelper.repl_fname);
           FStar_Parser_ParseIt.frag_text = text;
           FStar_Parser_ParseIt.frag_line = Prims.int_one;
           FStar_Parser_ParseIt.frag_col = Prims.int_zero
         } in
       let uu____1818 = ld_deps st in
       match uu____1818 with
       | FStar_Util.Inl (st1, deps) ->
           let names =
             add_module_completions
               st1.FStar_Interactive_JsonHelper.repl_fname deps
               st1.FStar_Interactive_JsonHelper.repl_names in
           repl_tx
             (let uu___341_1850 = st1 in
              {
                FStar_Interactive_JsonHelper.repl_line =
                  (uu___341_1850.FStar_Interactive_JsonHelper.repl_line);
                FStar_Interactive_JsonHelper.repl_column =
                  (uu___341_1850.FStar_Interactive_JsonHelper.repl_column);
                FStar_Interactive_JsonHelper.repl_fname =
                  (uu___341_1850.FStar_Interactive_JsonHelper.repl_fname);
                FStar_Interactive_JsonHelper.repl_deps_stack =
                  (uu___341_1850.FStar_Interactive_JsonHelper.repl_deps_stack);
                FStar_Interactive_JsonHelper.repl_curmod =
                  (uu___341_1850.FStar_Interactive_JsonHelper.repl_curmod);
                FStar_Interactive_JsonHelper.repl_env =
                  (uu___341_1850.FStar_Interactive_JsonHelper.repl_env);
                FStar_Interactive_JsonHelper.repl_stdin =
                  (uu___341_1850.FStar_Interactive_JsonHelper.repl_stdin);
                FStar_Interactive_JsonHelper.repl_names = names
              }) LaxCheck (FStar_Interactive_JsonHelper.PushFragment frag)
       | FStar_Util.Inr st1 -> (FStar_Pervasives_Native.None, st1))