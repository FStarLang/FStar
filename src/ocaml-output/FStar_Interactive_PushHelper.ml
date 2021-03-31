open Prims
type push_kind =
  | SyntaxCheck 
  | LaxCheck 
  | FullCheck 
let (uu___is_SyntaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | SyntaxCheck -> true | uu___ -> false
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee -> match projectee with | LaxCheck -> true | uu___ -> false
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee -> match projectee with | FullCheck -> true | uu___ -> false
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
      let uu___ = env in
      let uu___1 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
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
        FStar_TypeChecker_Env.top_level =
          (uu___.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq = (uu___.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.use_eq_strict =
          (uu___.FStar_TypeChecker_Env.use_eq_strict);
        FStar_TypeChecker_Env.is_iface =
          (uu___.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit = (uu___.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 = (uu___.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth = (uu___.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term = (uu___.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
          (uu___.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStar_TypeChecker_Env.universe_of =
          (uu___.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (uu___.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
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
        FStar_TypeChecker_Env.dsenv = uu___1;
        FStar_TypeChecker_Env.nbe = (uu___.FStar_TypeChecker_Env.nbe);
        FStar_TypeChecker_Env.strict_args_tab =
          (uu___.FStar_TypeChecker_Env.strict_args_tab);
        FStar_TypeChecker_Env.erasable_types_tab =
          (uu___.FStar_TypeChecker_Env.erasable_types_tab);
        FStar_TypeChecker_Env.enable_defer_to_tac =
          (uu___.FStar_TypeChecker_Env.enable_defer_to_tac);
        FStar_TypeChecker_Env.unif_allow_ref_guards =
          (uu___.FStar_TypeChecker_Env.unif_allow_ref_guards)
      }
let (repl_ld_tasks_of_deps :
  Prims.string Prims.list ->
    FStar_Interactive_JsonHelper.repl_task Prims.list ->
      FStar_Interactive_JsonHelper.repl_task Prims.list)
  =
  fun deps ->
    fun final_tasks ->
      let wrap fname =
        let uu___ = FStar_Util.now () in
        {
          FStar_Interactive_JsonHelper.tf_fname = fname;
          FStar_Interactive_JsonHelper.tf_modtime = uu___
        } in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu___ =
              let uu___1 =
                let uu___2 = wrap intf in
                let uu___3 = wrap impl in (uu___2, uu___3) in
              FStar_Interactive_JsonHelper.LDInterleaved uu___1 in
            let uu___1 = aux deps' final_tasks1 in uu___ :: uu___1
        | intf_or_impl::deps' ->
            let uu___ =
              let uu___1 = wrap intf_or_impl in
              FStar_Interactive_JsonHelper.LDSingle uu___1 in
            let uu___1 = aux deps' final_tasks1 in uu___ :: uu___1
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
      let uu___ = get_mod_name f in uu___ = our_mod_name in
    let parse_data_cache = FStar_CheckedFiles.load_parsing_data_from_cache in
    let uu___ =
      FStar_Dependencies.find_deps_if_needed [filename] parse_data_cache in
    match uu___ with
    | (deps, dep_graph) ->
        let uu___1 = FStar_List.partition has_our_mod_name deps in
        (match uu___1 with
         | (same_name, real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu___3 =
                       let uu___4 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu___4 in
                     if uu___3
                     then
                       let uu___4 =
                         let uu___5 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.Fatal_MissingInterface, uu___5) in
                       FStar_Errors.raise_err uu___4
                     else ());
                    (let uu___4 =
                       let uu___5 = FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu___5 in
                     if uu___4
                     then
                       let uu___5 =
                         let uu___6 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.Fatal_MissingImplementation, uu___6) in
                       FStar_Errors.raise_err uu___5
                     else ());
                    (let uu___4 =
                       let uu___5 =
                         let uu___6 = FStar_Util.now () in
                         {
                           FStar_Interactive_JsonHelper.tf_fname = intf;
                           FStar_Interactive_JsonHelper.tf_modtime = uu___6
                         } in
                       FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile
                         uu___5 in
                     [uu___4]))
               | impl::[] -> []
               | uu___2 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu___4 =
                       let uu___5 =
                         FStar_Util.format message [our_mod_name; mods_str] in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch, uu___5) in
                     FStar_Errors.raise_err uu___4);
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
      let uu___ = FStar_TypeChecker_Tc.snapshot_context env msg in
      match uu___ with
      | (ctx_depth, env1) ->
          let uu___1 = FStar_Options.snapshot () in
          (match uu___1 with
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
          let uu___ =
            snapshot_env st.FStar_Interactive_JsonHelper.repl_env msg in
          match uu___ with
          | (depth, env) ->
              ((let uu___2 =
                  let uu___3 = FStar_ST.op_Bang repl_stack in
                  (depth, (task, st)) :: uu___3 in
                FStar_ST.op_Colon_Equals repl_stack uu___2);
               (let uu___2 = st in
                let uu___3 = set_check_kind env push_kind1 in
                {
                  FStar_Interactive_JsonHelper.repl_line =
                    (uu___2.FStar_Interactive_JsonHelper.repl_line);
                  FStar_Interactive_JsonHelper.repl_column =
                    (uu___2.FStar_Interactive_JsonHelper.repl_column);
                  FStar_Interactive_JsonHelper.repl_fname =
                    (uu___2.FStar_Interactive_JsonHelper.repl_fname);
                  FStar_Interactive_JsonHelper.repl_deps_stack =
                    (uu___2.FStar_Interactive_JsonHelper.repl_deps_stack);
                  FStar_Interactive_JsonHelper.repl_curmod =
                    (uu___2.FStar_Interactive_JsonHelper.repl_curmod);
                  FStar_Interactive_JsonHelper.repl_env = uu___3;
                  FStar_Interactive_JsonHelper.repl_stdin =
                    (uu___2.FStar_Interactive_JsonHelper.repl_stdin);
                  FStar_Interactive_JsonHelper.repl_names =
                    (uu___2.FStar_Interactive_JsonHelper.repl_names)
                }))
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver ->
    fun msg ->
      fun uu___ ->
        match uu___ with
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
      let uu___ = FStar_ST.op_Bang repl_stack in
      match uu___ with
      | [] -> failwith "Too many pops"
      | (depth, (uu___1, st'))::stack_tl ->
          let env =
            rollback_env
              (st.FStar_Interactive_JsonHelper.repl_env).FStar_TypeChecker_Env.solver
              msg depth in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu___4 =
              FStar_Util.physical_equality env
                st'.FStar_Interactive_JsonHelper.repl_env in
            FStar_Common.runtime_assert uu___4 "Inconsistent stack state");
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
          let uu___ =
            let uu___1 = FStar_TypeChecker_Env.dep_graph env in
            FStar_Parser_Dep.parsing_data_of uu___1 in
          FStar_All.pipe_right modf uu___ in
        let uu___ =
          FStar_Universal.tc_one_file_for_ide env intf_opt modf parse_data in
        match uu___ with | (uu___1, env1) -> env1
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
            let uu___ =
              tc_one env
                (FStar_Pervasives_Native.Some
                   (intf.FStar_Interactive_JsonHelper.tf_fname))
                impl.FStar_Interactive_JsonHelper.tf_fname in
            (curmod, uu___)
        | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
            let uu___ =
              tc_one env FStar_Pervasives_Native.None
                intf_or_impl.FStar_Interactive_JsonHelper.tf_fname in
            (curmod, uu___)
        | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
            let uu___ =
              FStar_Universal.load_interface_decls env
                intf.FStar_Interactive_JsonHelper.tf_fname in
            (curmod, uu___)
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
  fun projectee -> match projectee with | NTAlias _0 -> true | uu___ -> false
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee -> match projectee with | NTAlias _0 -> _0
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee -> match projectee with | NTOpen _0 -> true | uu___ -> false
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee -> match projectee with | NTOpen _0 -> _0
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTInclude _0 -> true | uu___ -> false
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee -> match projectee with | NTInclude _0 -> _0
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTBinding _0 -> true | uu___ -> false
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
    let uu___ =
      let uu___1 = FStar_Ident.ns_of_lid lid in
      let uu___2 = let uu___3 = FStar_Ident.ident_of_lid lid in [uu___3] in
      FStar_List.append uu___1 uu___2 in
    query_of_ids uu___
let (update_names_from_event :
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod_str ->
    fun table ->
      fun evt ->
        let is_cur_mod lid =
          let uu___ = FStar_Ident.string_of_lid lid in uu___ = cur_mod_str in
        match evt with
        | NTAlias (host, id, included) ->
            let uu___ = is_cur_mod host in
            if uu___
            then
              let uu___1 = FStar_Ident.string_of_id id in
              let uu___2 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table uu___1
                [] uu___2
            else table
        | NTOpen (host, (included, kind)) ->
            let uu___ = is_cur_mod host in
            if uu___
            then
              let uu___1 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu___1
            else table
        | NTInclude (host, included) ->
            let uu___ =
              let uu___1 = is_cur_mod host in
              if uu___1 then [] else query_of_lid host in
            let uu___1 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table uu___
              uu___1
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid (lid, uu___))
                  -> [lid]
              | FStar_Util.Inr (lids1, uu___) -> lids1
              | uu___ -> [] in
            FStar_List.fold_left
              (fun tbl ->
                 fun lid ->
                   let ns_query =
                     let uu___ =
                       let uu___1 = FStar_Ident.nsstr lid in
                       uu___1 = cur_mod_str in
                     if uu___
                     then []
                     else
                       (let uu___2 = FStar_Ident.ns_of_lid lid in
                        query_of_ids uu___2) in
                   let uu___ =
                     let uu___1 = FStar_Ident.ident_of_lid lid in
                     FStar_Ident.string_of_id uu___1 in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu___ lid) table lids
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
              let uu___ = FStar_Syntax_Syntax.mod_name md in
              FStar_Ident.string_of_lid uu___ in
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
      let uu___ = st in
      {
        FStar_Interactive_JsonHelper.repl_line =
          (uu___.FStar_Interactive_JsonHelper.repl_line);
        FStar_Interactive_JsonHelper.repl_column =
          (uu___.FStar_Interactive_JsonHelper.repl_column);
        FStar_Interactive_JsonHelper.repl_fname =
          (uu___.FStar_Interactive_JsonHelper.repl_fname);
        FStar_Interactive_JsonHelper.repl_deps_stack =
          (uu___.FStar_Interactive_JsonHelper.repl_deps_stack);
        FStar_Interactive_JsonHelper.repl_curmod =
          (uu___.FStar_Interactive_JsonHelper.repl_curmod);
        FStar_Interactive_JsonHelper.repl_env =
          (uu___.FStar_Interactive_JsonHelper.repl_env);
        FStar_Interactive_JsonHelper.repl_stdin =
          (uu___.FStar_Interactive_JsonHelper.repl_stdin);
        FStar_Interactive_JsonHelper.repl_names = names
      }
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu___ ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu___1 = let uu___2 = FStar_ST.op_Bang events in evt :: uu___2 in
      FStar_ST.op_Colon_Equals events uu___1 in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv ->
             fun op ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_DsEnv.current_module dsenv in
                   (uu___3, op) in
                 NTOpen uu___2 in
               push_event uu___1);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv ->
             fun ns ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_DsEnv.current_module dsenv in
                   (uu___3, ns) in
                 NTInclude uu___2 in
               push_event uu___1);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv ->
             fun x ->
               fun l ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_Syntax_DsEnv.current_module dsenv in
                     (uu___3, x, l) in
                   NTAlias uu___2 in
                 push_event uu___1)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu___1 -> fun s -> push_event (NTBinding s))
      })
let (track_name_changes :
  FStar_TypeChecker_Env.env_t ->
    (FStar_TypeChecker_Env.env_t *
      (FStar_TypeChecker_Env.env_t ->
         (FStar_TypeChecker_Env.env_t * name_tracking_event Prims.list))))
  =
  fun env ->
    let set_hooks dshooks tchooks env1 =
      let uu___ =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv ->
             let uu___1 = FStar_Syntax_DsEnv.set_ds_hooks dsenv dshooks in
             ((), uu___1)) in
      match uu___ with
      | ((), tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu___ =
      let uu___1 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu___2 = FStar_TypeChecker_Env.tc_hooks env in (uu___1, uu___2) in
    match uu___ with
    | (old_dshooks, old_tchooks) ->
        let uu___1 = fresh_name_tracking_hooks () in
        (match uu___1 with
         | (events, new_dshooks, new_tchooks) ->
             let uu___2 = set_hooks new_dshooks new_tchooks env in
             (uu___2,
               ((fun env1 ->
                   let uu___3 = set_hooks old_dshooks old_tchooks env1 in
                   let uu___4 =
                     let uu___5 = FStar_ST.op_Bang events in
                     FStar_List.rev uu___5 in
                   (uu___3, uu___4)))))
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
          (fun uu___ ->
             match () with
             | () ->
                 let st1 = push_repl "repl_tx" push_kind1 task st in
                 let uu___1 =
                   track_name_changes
                     st1.FStar_Interactive_JsonHelper.repl_env in
                 (match uu___1 with
                  | (env, finish_name_tracking) ->
                      let uu___2 =
                        run_repl_task
                          st1.FStar_Interactive_JsonHelper.repl_curmod env
                          task in
                      (match uu___2 with
                       | (curmod, env1) ->
                           let st2 =
                             let uu___3 = st1 in
                             {
                               FStar_Interactive_JsonHelper.repl_line =
                                 (uu___3.FStar_Interactive_JsonHelper.repl_line);
                               FStar_Interactive_JsonHelper.repl_column =
                                 (uu___3.FStar_Interactive_JsonHelper.repl_column);
                               FStar_Interactive_JsonHelper.repl_fname =
                                 (uu___3.FStar_Interactive_JsonHelper.repl_fname);
                               FStar_Interactive_JsonHelper.repl_deps_stack =
                                 (uu___3.FStar_Interactive_JsonHelper.repl_deps_stack);
                               FStar_Interactive_JsonHelper.repl_curmod =
                                 curmod;
                               FStar_Interactive_JsonHelper.repl_env = env1;
                               FStar_Interactive_JsonHelper.repl_stdin =
                                 (uu___3.FStar_Interactive_JsonHelper.repl_stdin);
                               FStar_Interactive_JsonHelper.repl_names =
                                 (uu___3.FStar_Interactive_JsonHelper.repl_names)
                             } in
                           let uu___3 = finish_name_tracking env1 in
                           (match uu___3 with
                            | (env2, name_events) ->
                                let uu___4 =
                                  commit_name_tracking st2 name_events in
                                (FStar_Pervasives_Native.None, uu___4))))) ()
        with
        | FStar_All.Failure msg ->
            let uu___1 =
              let uu___2 =
                FStar_Interactive_JsonHelper.js_diag
                  st.FStar_Interactive_JsonHelper.repl_fname msg
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu___2 in
            (uu___1, st)
        | FStar_Util.SigInt ->
            (FStar_Util.print_error "[E] Interrupt";
             (FStar_Pervasives_Native.None, st))
        | FStar_Errors.Error (e, msg, r, _ctx) ->
            let uu___1 =
              let uu___2 =
                FStar_Interactive_JsonHelper.js_diag
                  st.FStar_Interactive_JsonHelper.repl_fname msg
                  (FStar_Pervasives_Native.Some r) in
              FStar_Pervasives_Native.Some uu___2 in
            (uu___1, st)
        | FStar_Errors.Err (e, msg, _ctx) ->
            let uu___1 =
              let uu___2 =
                FStar_Interactive_JsonHelper.js_diag
                  st.FStar_Interactive_JsonHelper.repl_fname msg
                  FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some uu___2 in
            (uu___1, st)
        | FStar_Errors.Stop ->
            (FStar_Util.print_error "[E] Stop";
             (FStar_Pervasives_Native.None, st))
let (tf_of_fname : Prims.string -> FStar_Interactive_JsonHelper.timed_fname)
  =
  fun fname ->
    let uu___ = FStar_Parser_ParseIt.get_file_last_modification_time fname in
    {
      FStar_Interactive_JsonHelper.tf_fname = fname;
      FStar_Interactive_JsonHelper.tf_modtime = uu___
    }
let (update_task_timestamps :
  FStar_Interactive_JsonHelper.repl_task ->
    FStar_Interactive_JsonHelper.repl_task)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Interactive_JsonHelper.LDInterleaved (intf, impl) ->
        let uu___1 =
          let uu___2 = tf_of_fname intf.FStar_Interactive_JsonHelper.tf_fname in
          let uu___3 = tf_of_fname impl.FStar_Interactive_JsonHelper.tf_fname in
          (uu___2, uu___3) in
        FStar_Interactive_JsonHelper.LDInterleaved uu___1
    | FStar_Interactive_JsonHelper.LDSingle intf_or_impl ->
        let uu___1 =
          tf_of_fname intf_or_impl.FStar_Interactive_JsonHelper.tf_fname in
        FStar_Interactive_JsonHelper.LDSingle uu___1
    | FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu___1 = tf_of_fname intf.FStar_Interactive_JsonHelper.tf_fname in
        FStar_Interactive_JsonHelper.LDInterfaceOfCurrentFile uu___1
    | other -> other
let (repl_ldtx :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Interactive_JsonHelper.repl_task Prims.list -> either_replst)
  =
  fun st ->
    fun tasks ->
      let rec revert_many st1 uu___ =
        match uu___ with
        | [] -> st1
        | (_id, (task, _st'))::entries ->
            let st' = pop_repl "repl_ldtx" st1 in
            let dep_graph =
              FStar_TypeChecker_Env.dep_graph
                st1.FStar_Interactive_JsonHelper.repl_env in
            let st'1 =
              let uu___1 = st' in
              let uu___2 =
                FStar_TypeChecker_Env.set_dep_graph
                  st'.FStar_Interactive_JsonHelper.repl_env dep_graph in
              {
                FStar_Interactive_JsonHelper.repl_line =
                  (uu___1.FStar_Interactive_JsonHelper.repl_line);
                FStar_Interactive_JsonHelper.repl_column =
                  (uu___1.FStar_Interactive_JsonHelper.repl_column);
                FStar_Interactive_JsonHelper.repl_fname =
                  (uu___1.FStar_Interactive_JsonHelper.repl_fname);
                FStar_Interactive_JsonHelper.repl_deps_stack =
                  (uu___1.FStar_Interactive_JsonHelper.repl_deps_stack);
                FStar_Interactive_JsonHelper.repl_curmod =
                  (uu___1.FStar_Interactive_JsonHelper.repl_curmod);
                FStar_Interactive_JsonHelper.repl_env = uu___2;
                FStar_Interactive_JsonHelper.repl_stdin =
                  (uu___1.FStar_Interactive_JsonHelper.repl_stdin);
                FStar_Interactive_JsonHelper.repl_names =
                  (uu___1.FStar_Interactive_JsonHelper.repl_names)
              } in
            revert_many st'1 entries in
      let rec aux st1 tasks1 previous =
        match (tasks1, previous) with
        | ([], []) -> FStar_Util.Inl st1
        | (task::tasks2, []) ->
            let timestamped_task = update_task_timestamps task in
            let uu___ = repl_tx st1 LaxCheck timestamped_task in
            (match uu___ with
             | (diag, st2) ->
                 if Prims.op_Negation (FStar_Util.is_some diag)
                 then
                   let uu___1 =
                     let uu___2 = st2 in
                     let uu___3 = FStar_ST.op_Bang repl_stack in
                     {
                       FStar_Interactive_JsonHelper.repl_line =
                         (uu___2.FStar_Interactive_JsonHelper.repl_line);
                       FStar_Interactive_JsonHelper.repl_column =
                         (uu___2.FStar_Interactive_JsonHelper.repl_column);
                       FStar_Interactive_JsonHelper.repl_fname =
                         (uu___2.FStar_Interactive_JsonHelper.repl_fname);
                       FStar_Interactive_JsonHelper.repl_deps_stack = uu___3;
                       FStar_Interactive_JsonHelper.repl_curmod =
                         (uu___2.FStar_Interactive_JsonHelper.repl_curmod);
                       FStar_Interactive_JsonHelper.repl_env =
                         (uu___2.FStar_Interactive_JsonHelper.repl_env);
                       FStar_Interactive_JsonHelper.repl_stdin =
                         (uu___2.FStar_Interactive_JsonHelper.repl_stdin);
                       FStar_Interactive_JsonHelper.repl_names =
                         (uu___2.FStar_Interactive_JsonHelper.repl_names)
                     } in
                   aux uu___1 tasks2 []
                 else FStar_Util.Inr st2)
        | (task::tasks2, prev::previous1) when
            let uu___ = update_task_timestamps task in
            (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
              = uu___
            -> aux st1 tasks2 previous1
        | (tasks2, previous1) ->
            let uu___ = revert_many st1 previous1 in aux uu___ tasks2 [] in
      aux st tasks
        (FStar_List.rev st.FStar_Interactive_JsonHelper.repl_deps_stack)
let (ld_deps :
  FStar_Interactive_JsonHelper.repl_state ->
    ((FStar_Interactive_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_Interactive_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let uu___1 =
               deps_and_repl_ld_tasks_of_our_file
                 st.FStar_Interactive_JsonHelper.repl_fname in
             (match uu___1 with
              | (deps, tasks, dep_graph) ->
                  let st1 =
                    let uu___2 = st in
                    let uu___3 =
                      FStar_TypeChecker_Env.set_dep_graph
                        st.FStar_Interactive_JsonHelper.repl_env dep_graph in
                    {
                      FStar_Interactive_JsonHelper.repl_line =
                        (uu___2.FStar_Interactive_JsonHelper.repl_line);
                      FStar_Interactive_JsonHelper.repl_column =
                        (uu___2.FStar_Interactive_JsonHelper.repl_column);
                      FStar_Interactive_JsonHelper.repl_fname =
                        (uu___2.FStar_Interactive_JsonHelper.repl_fname);
                      FStar_Interactive_JsonHelper.repl_deps_stack =
                        (uu___2.FStar_Interactive_JsonHelper.repl_deps_stack);
                      FStar_Interactive_JsonHelper.repl_curmod =
                        (uu___2.FStar_Interactive_JsonHelper.repl_curmod);
                      FStar_Interactive_JsonHelper.repl_env = uu___3;
                      FStar_Interactive_JsonHelper.repl_stdin =
                        (uu___2.FStar_Interactive_JsonHelper.repl_stdin);
                      FStar_Interactive_JsonHelper.repl_names =
                        (uu___2.FStar_Interactive_JsonHelper.repl_names)
                    } in
                  let uu___2 = repl_ldtx st1 tasks in
                  (match uu___2 with
                   | FStar_Util.Inr st2 -> FStar_Util.Inr st2
                   | FStar_Util.Inl st2 -> FStar_Util.Inl (st2, deps)))) ()
    with
    | uu___ ->
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
             let uu___1 =
               FStar_String.substring str Prims.int_one
                 ((FStar_String.length str) - Prims.int_one) in
             Prims.op_Hat (FStar_String.uppercase first) uu___1) in
        let mods = FStar_Parser_Dep.build_inclusion_candidates_list () in
        let loaded_mods_set =
          let uu___ = FStar_Util.psmap_empty () in
          let uu___1 = let uu___2 = FStar_Options.prims () in uu___2 :: deps in
          FStar_List.fold_left
            (fun acc ->
               fun dep ->
                 let uu___2 = FStar_Parser_Dep.lowercase_module_name dep in
                 FStar_Util.psmap_add acc uu___2 true) uu___ uu___1 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1 ->
             fun uu___ ->
               match uu___ with
               | (modname, mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu___2 = capitalize modname in
                        FStar_Util.split uu___2 "." in
                      let uu___2 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu___2 mod_path ns_query)) table
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
       let uu___1 = ld_deps st in
       match uu___1 with
       | FStar_Util.Inl (st1, deps) ->
           let names =
             add_module_completions
               st1.FStar_Interactive_JsonHelper.repl_fname deps
               st1.FStar_Interactive_JsonHelper.repl_names in
           repl_tx
             (let uu___2 = st1 in
              {
                FStar_Interactive_JsonHelper.repl_line =
                  (uu___2.FStar_Interactive_JsonHelper.repl_line);
                FStar_Interactive_JsonHelper.repl_column =
                  (uu___2.FStar_Interactive_JsonHelper.repl_column);
                FStar_Interactive_JsonHelper.repl_fname =
                  (uu___2.FStar_Interactive_JsonHelper.repl_fname);
                FStar_Interactive_JsonHelper.repl_deps_stack =
                  (uu___2.FStar_Interactive_JsonHelper.repl_deps_stack);
                FStar_Interactive_JsonHelper.repl_curmod =
                  (uu___2.FStar_Interactive_JsonHelper.repl_curmod);
                FStar_Interactive_JsonHelper.repl_env =
                  (uu___2.FStar_Interactive_JsonHelper.repl_env);
                FStar_Interactive_JsonHelper.repl_stdin =
                  (uu___2.FStar_Interactive_JsonHelper.repl_stdin);
                FStar_Interactive_JsonHelper.repl_names = names
              }) LaxCheck (FStar_Interactive_JsonHelper.PushFragment frag)
       | FStar_Util.Inr st1 -> (FStar_Pervasives_Native.None, st1))