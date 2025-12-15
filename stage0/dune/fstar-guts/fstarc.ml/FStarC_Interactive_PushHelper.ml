open Prims
type ctx_depth_t =
  (Prims.int * Prims.int * FStarC_TypeChecker_Env.solver_depth_t * Prims.int)
type deps_t = FStarC_Parser_Dep.deps
type either_replst =
  (FStarC_Interactive_Ide_Types.repl_state,
    FStarC_Interactive_Ide_Types.repl_state) FStar_Pervasives.either
type name_tracking_event =
  | NTAlias of (FStarC_Ident.lid * FStarC_Ident.ident * FStarC_Ident.lid) 
  | NTOpen of (FStarC_Ident.lid *
  FStarC_Syntax_Syntax.open_module_or_namespace) 
  | NTInclude of (FStarC_Ident.lid * FStarC_Ident.lid) 
  | NTBinding of (FStarC_Syntax_Syntax.binding,
  FStarC_TypeChecker_Env.sig_binding) FStar_Pervasives.either 
let uu___is_NTAlias (projectee : name_tracking_event) : Prims.bool=
  match projectee with | NTAlias _0 -> true | uu___ -> false
let __proj__NTAlias__item___0 (projectee : name_tracking_event) :
  (FStarC_Ident.lid * FStarC_Ident.ident * FStarC_Ident.lid)=
  match projectee with | NTAlias _0 -> _0
let uu___is_NTOpen (projectee : name_tracking_event) : Prims.bool=
  match projectee with | NTOpen _0 -> true | uu___ -> false
let __proj__NTOpen__item___0 (projectee : name_tracking_event) :
  (FStarC_Ident.lid * FStarC_Syntax_Syntax.open_module_or_namespace)=
  match projectee with | NTOpen _0 -> _0
let uu___is_NTInclude (projectee : name_tracking_event) : Prims.bool=
  match projectee with | NTInclude _0 -> true | uu___ -> false
let __proj__NTInclude__item___0 (projectee : name_tracking_event) :
  (FStarC_Ident.lid * FStarC_Ident.lid)=
  match projectee with | NTInclude _0 -> _0
let uu___is_NTBinding (projectee : name_tracking_event) : Prims.bool=
  match projectee with | NTBinding _0 -> true | uu___ -> false
let __proj__NTBinding__item___0 (projectee : name_tracking_event) :
  (FStarC_Syntax_Syntax.binding, FStarC_TypeChecker_Env.sig_binding)
    FStar_Pervasives.either=
  match projectee with | NTBinding _0 -> _0
let repl_stack : FStarC_Interactive_Ide_Types.repl_stack_t FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let set_check_kind (env : FStarC_TypeChecker_Env.env_t)
  (check_kind : FStarC_Interactive_Ide_Types.push_kind) :
  FStarC_TypeChecker_Env.env_t=
  let uu___ =
    (check_kind = FStarC_Interactive_Ide_Types.LaxCheck) ||
      (FStarC_Options.lax ()) in
  let uu___1 =
    FStarC_Syntax_DsEnv.set_syntax_only env.FStarC_TypeChecker_Env.dsenv
      (check_kind = FStarC_Interactive_Ide_Types.SyntaxCheck) in
  {
    FStarC_TypeChecker_Env.solver = (env.FStarC_TypeChecker_Env.solver);
    FStarC_TypeChecker_Env.range = (env.FStarC_TypeChecker_Env.range);
    FStarC_TypeChecker_Env.curmodule = (env.FStarC_TypeChecker_Env.curmodule);
    FStarC_TypeChecker_Env.gamma = (env.FStarC_TypeChecker_Env.gamma);
    FStarC_TypeChecker_Env.gamma_sig = (env.FStarC_TypeChecker_Env.gamma_sig);
    FStarC_TypeChecker_Env.gamma_cache =
      (env.FStarC_TypeChecker_Env.gamma_cache);
    FStarC_TypeChecker_Env.modules = (env.FStarC_TypeChecker_Env.modules);
    FStarC_TypeChecker_Env.expected_typ =
      (env.FStarC_TypeChecker_Env.expected_typ);
    FStarC_TypeChecker_Env.sigtab = (env.FStarC_TypeChecker_Env.sigtab);
    FStarC_TypeChecker_Env.attrtab = (env.FStarC_TypeChecker_Env.attrtab);
    FStarC_TypeChecker_Env.instantiate_imp =
      (env.FStarC_TypeChecker_Env.instantiate_imp);
    FStarC_TypeChecker_Env.effects = (env.FStarC_TypeChecker_Env.effects);
    FStarC_TypeChecker_Env.generalize =
      (env.FStarC_TypeChecker_Env.generalize);
    FStarC_TypeChecker_Env.letrecs = (env.FStarC_TypeChecker_Env.letrecs);
    FStarC_TypeChecker_Env.top_level = (env.FStarC_TypeChecker_Env.top_level);
    FStarC_TypeChecker_Env.check_uvars =
      (env.FStarC_TypeChecker_Env.check_uvars);
    FStarC_TypeChecker_Env.use_eq_strict =
      (env.FStarC_TypeChecker_Env.use_eq_strict);
    FStarC_TypeChecker_Env.is_iface = (env.FStarC_TypeChecker_Env.is_iface);
    FStarC_TypeChecker_Env.admit = uu___;
    FStarC_TypeChecker_Env.phase1 = (env.FStarC_TypeChecker_Env.phase1);
    FStarC_TypeChecker_Env.failhard = (env.FStarC_TypeChecker_Env.failhard);
    FStarC_TypeChecker_Env.flychecking =
      (env.FStarC_TypeChecker_Env.flychecking);
    FStarC_TypeChecker_Env.uvar_subtyping =
      (env.FStarC_TypeChecker_Env.uvar_subtyping);
    FStarC_TypeChecker_Env.intactics = (env.FStarC_TypeChecker_Env.intactics);
    FStarC_TypeChecker_Env.nocoerce = (env.FStarC_TypeChecker_Env.nocoerce);
    FStarC_TypeChecker_Env.tc_term = (env.FStarC_TypeChecker_Env.tc_term);
    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
      (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
    FStarC_TypeChecker_Env.universe_of =
      (env.FStarC_TypeChecker_Env.universe_of);
    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
      (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
    FStarC_TypeChecker_Env.teq_nosmt_force =
      (env.FStarC_TypeChecker_Env.teq_nosmt_force);
    FStarC_TypeChecker_Env.subtype_nosmt_force =
      (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
    FStarC_TypeChecker_Env.qtbl_name_and_index =
      (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
    FStarC_TypeChecker_Env.normalized_eff_names =
      (env.FStarC_TypeChecker_Env.normalized_eff_names);
    FStarC_TypeChecker_Env.fv_delta_depths =
      (env.FStarC_TypeChecker_Env.fv_delta_depths);
    FStarC_TypeChecker_Env.proof_ns = (env.FStarC_TypeChecker_Env.proof_ns);
    FStarC_TypeChecker_Env.synth_hook =
      (env.FStarC_TypeChecker_Env.synth_hook);
    FStarC_TypeChecker_Env.try_solve_implicits_hook =
      (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
    FStarC_TypeChecker_Env.splice = (env.FStarC_TypeChecker_Env.splice);
    FStarC_TypeChecker_Env.mpreprocess =
      (env.FStarC_TypeChecker_Env.mpreprocess);
    FStarC_TypeChecker_Env.postprocess =
      (env.FStarC_TypeChecker_Env.postprocess);
    FStarC_TypeChecker_Env.identifier_info =
      (env.FStarC_TypeChecker_Env.identifier_info);
    FStarC_TypeChecker_Env.tc_hooks = (env.FStarC_TypeChecker_Env.tc_hooks);
    FStarC_TypeChecker_Env.dsenv = uu___1;
    FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
    FStarC_TypeChecker_Env.strict_args_tab =
      (env.FStarC_TypeChecker_Env.strict_args_tab);
    FStarC_TypeChecker_Env.erasable_types_tab =
      (env.FStarC_TypeChecker_Env.erasable_types_tab);
    FStarC_TypeChecker_Env.enable_defer_to_tac =
      (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
    FStarC_TypeChecker_Env.unif_allow_ref_guards =
      (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
    FStarC_TypeChecker_Env.erase_erasable_args =
      (env.FStarC_TypeChecker_Env.erase_erasable_args);
    FStarC_TypeChecker_Env.core_check =
      (env.FStarC_TypeChecker_Env.core_check);
    FStarC_TypeChecker_Env.missing_decl =
      (env.FStarC_TypeChecker_Env.missing_decl)
  }
let repl_ld_tasks_of_deps (deps : Prims.string Prims.list)
  (final_tasks : FStarC_Interactive_Ide_Types.repl_task Prims.list) :
  FStarC_Interactive_Ide_Types.repl_task Prims.list=
  let wrap fname =
    let uu___ = FStarC_Time.get_time_of_day () in
    {
      FStarC_Interactive_Ide_Types.tf_fname = fname;
      FStarC_Interactive_Ide_Types.tf_modtime = uu___
    } in
  let rec aux deps1 final_tasks1 =
    match deps1 with
    | intf::impl::deps' when FStarC_Universal.needs_interleaving intf impl ->
        let uu___ =
          let uu___1 =
            let uu___2 = wrap intf in
            let uu___3 = wrap impl in (uu___2, uu___3) in
          FStarC_Interactive_Ide_Types.LDInterleaved uu___1 in
        let uu___1 = aux deps' final_tasks1 in uu___ :: uu___1
    | intf_or_impl::deps' ->
        let uu___ =
          let uu___1 = wrap intf_or_impl in
          FStarC_Interactive_Ide_Types.LDSingle uu___1 in
        let uu___1 = aux deps' final_tasks1 in uu___ :: uu___1
    | [] -> final_tasks1 in
  aux deps final_tasks
let deps_and_repl_ld_tasks_of_our_file (filename : Prims.string) :
  (Prims.string Prims.list * FStarC_Interactive_Ide_Types.repl_task
    Prims.list * deps_t)=
  let get_mod_name fname = FStarC_Parser_Dep.lowercase_module_name fname in
  let our_mod_name = get_mod_name filename in
  let has_our_mod_name f = let uu___ = get_mod_name f in uu___ = our_mod_name in
  let parse_data_cache = FStarC_CheckedFiles.load_parsing_data_from_cache in
  let uu___ =
    FStarC_Dependencies.find_deps_if_needed [filename] parse_data_cache in
  match uu___ with
  | (deps, dep_graph) ->
      let uu___1 = FStarC_List.partition has_our_mod_name deps in
      (match uu___1 with
       | (same_name, real_deps) ->
           let intf_tasks =
             match same_name with
             | intf::impl::[] ->
                 ((let uu___3 =
                     let uu___4 = FStarC_Parser_Dep.is_interface intf in
                     Prims.op_Negation uu___4 in
                   if uu___3
                   then
                     let uu___4 =
                       FStarC_Format.fmt1 "Expecting an interface, got %s"
                         intf in
                     FStarC_Errors.raise_error0
                       FStarC_Errors_Codes.Fatal_MissingInterface ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                       (Obj.magic uu___4)
                   else ());
                  (let uu___4 =
                     let uu___5 = FStarC_Parser_Dep.is_implementation impl in
                     Prims.op_Negation uu___5 in
                   if uu___4
                   then
                     let uu___5 =
                       FStarC_Format.fmt1
                         "Expecting an implementation, got %s" impl in
                     FStarC_Errors.raise_error0
                       FStarC_Errors_Codes.Fatal_MissingImplementation ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                       (Obj.magic uu___5)
                   else ());
                  (let uu___4 =
                     let uu___5 =
                       let uu___6 = FStarC_Time.get_time_of_day () in
                       {
                         FStarC_Interactive_Ide_Types.tf_fname = intf;
                         FStarC_Interactive_Ide_Types.tf_modtime = uu___6
                       } in
                     FStarC_Interactive_Ide_Types.LDInterfaceOfCurrentFile
                       uu___5 in
                   [uu___4]))
             | impl::[] -> []
             | uu___2 ->
                 let mods_str = FStarC_String.concat " " same_name in
                 let message = "Too many or too few files matching %s: %s" in
                 ((let uu___4 =
                     FStarC_Format.fmt message [our_mod_name; mods_str] in
                   FStarC_Errors.raise_error0
                     FStarC_Errors_Codes.Fatal_TooManyOrTooFewFileMatch ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                     (Obj.magic uu___4));
                  []) in
           let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
           (real_deps, tasks, dep_graph))
let snapshot_env (env : FStarC_TypeChecker_Env.env) (msg : Prims.string) :
  (FStarC_Interactive_Ide_Types.repl_depth_t * FStarC_TypeChecker_Env.env_t)=
  let uu___ = FStarC_TypeChecker_Tc.snapshot_context env msg in
  match uu___ with
  | (ctx_depth, env1) ->
      let uu___1 = FStarC_Options.snapshot () in
      (match uu___1 with | (opt_depth, ()) -> ((ctx_depth, opt_depth), env1))
let push_repl (msg : Prims.string)
  (push_kind_opt :
    FStarC_Interactive_Ide_Types.push_kind FStar_Pervasives_Native.option)
  (task : FStarC_Interactive_Ide_Types.repl_task)
  (st : FStarC_Interactive_Ide_Types.repl_state) :
  FStarC_Interactive_Ide_Types.repl_state=
  let uu___ = snapshot_env st.FStarC_Interactive_Ide_Types.repl_env msg in
  match uu___ with
  | (depth, env) ->
      ((let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang repl_stack in
          (depth,
            (task,
              {
                FStarC_Interactive_Ide_Types.repl_line =
                  (st.FStarC_Interactive_Ide_Types.repl_line);
                FStarC_Interactive_Ide_Types.repl_column =
                  (st.FStarC_Interactive_Ide_Types.repl_column);
                FStarC_Interactive_Ide_Types.repl_fname =
                  (st.FStarC_Interactive_Ide_Types.repl_fname);
                FStarC_Interactive_Ide_Types.repl_deps_stack =
                  (st.FStarC_Interactive_Ide_Types.repl_deps_stack);
                FStarC_Interactive_Ide_Types.repl_curmod =
                  (st.FStarC_Interactive_Ide_Types.repl_curmod);
                FStarC_Interactive_Ide_Types.repl_env =
                  (st.FStarC_Interactive_Ide_Types.repl_env);
                FStarC_Interactive_Ide_Types.repl_stdin =
                  (st.FStarC_Interactive_Ide_Types.repl_stdin);
                FStarC_Interactive_Ide_Types.repl_names =
                  (st.FStarC_Interactive_Ide_Types.repl_names);
                FStarC_Interactive_Ide_Types.repl_buffered_input_queries = [];
                FStarC_Interactive_Ide_Types.repl_lang =
                  (st.FStarC_Interactive_Ide_Types.repl_lang)
              }))
            :: uu___3 in
        FStarC_Effect.op_Colon_Equals repl_stack uu___2);
       (match push_kind_opt with
        | FStar_Pervasives_Native.None -> st
        | FStar_Pervasives_Native.Some push_kind ->
            let uu___2 = set_check_kind env push_kind in
            {
              FStarC_Interactive_Ide_Types.repl_line =
                (st.FStarC_Interactive_Ide_Types.repl_line);
              FStarC_Interactive_Ide_Types.repl_column =
                (st.FStarC_Interactive_Ide_Types.repl_column);
              FStarC_Interactive_Ide_Types.repl_fname =
                (st.FStarC_Interactive_Ide_Types.repl_fname);
              FStarC_Interactive_Ide_Types.repl_deps_stack =
                (st.FStarC_Interactive_Ide_Types.repl_deps_stack);
              FStarC_Interactive_Ide_Types.repl_curmod =
                (st.FStarC_Interactive_Ide_Types.repl_curmod);
              FStarC_Interactive_Ide_Types.repl_env = uu___2;
              FStarC_Interactive_Ide_Types.repl_stdin =
                (st.FStarC_Interactive_Ide_Types.repl_stdin);
              FStarC_Interactive_Ide_Types.repl_names =
                (st.FStarC_Interactive_Ide_Types.repl_names);
              FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
                (st.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
              FStarC_Interactive_Ide_Types.repl_lang =
                (st.FStarC_Interactive_Ide_Types.repl_lang)
            }))
let adjust_topmost_push_frag
  (f :
    FStarC_Interactive_Ide_Types.repl_task ->
      FStarC_Interactive_Ide_Types.repl_task)
  : unit=
  let uu___ = FStarC_Effect.op_Bang repl_stack in
  match uu___ with
  | (depth, (FStarC_Interactive_Ide_Types.PushFragment x, st))::rest ->
      let pf = f (FStarC_Interactive_Ide_Types.PushFragment x) in
      FStarC_Effect.op_Colon_Equals repl_stack ((depth, (pf, st)) :: rest)
  | uu___1 -> ()
let add_issues_to_push_fragment (issues : FStarC_Json.json Prims.list) :
  unit=
  let adjust uu___ =
    match uu___ with
    | FStarC_Interactive_Ide_Types.PushFragment (frag, push_kind, i, deps) ->
        FStarC_Interactive_Ide_Types.PushFragment
          (frag, push_kind, (FStarC_List.op_At issues i), deps) in
  adjust_topmost_push_frag adjust
let add_filenames_to_push_fragment (deps : Prims.string Prims.list) : 
  unit=
  let adjust uu___ =
    match uu___ with
    | FStarC_Interactive_Ide_Types.PushFragment (frag, push_kind, i, deps')
        ->
        FStarC_Interactive_Ide_Types.PushFragment
          (frag, push_kind, i, (FStarC_List.op_At deps deps')) in
  adjust_topmost_push_frag adjust
let rollback_env (solver : FStarC_TypeChecker_Env.solver_t)
  (msg : Prims.string)
  (uu___ :
    ((Prims.int * Prims.int * FStarC_TypeChecker_Env.solver_depth_t *
      Prims.int) * Prims.int))
  : FStarC_TypeChecker_Env.env=
  match uu___ with
  | (ctx_depth, opt_depth) ->
      let env =
        FStarC_TypeChecker_Tc.rollback_context solver msg
          (FStar_Pervasives_Native.Some ctx_depth) in
      (FStarC_Options.rollback (FStar_Pervasives_Native.Some opt_depth); env)
let should_reset (task : FStarC_Interactive_Ide_Types.repl_task) :
  Prims.bool=
  match task with
  | FStarC_Interactive_Ide_Types.PushFragment (uu___, uu___1, uu___2, deps)
      -> Prims.uu___is_Cons deps
  | uu___ -> false
let pop_repl (msg : Prims.string)
  (st : FStarC_Interactive_Ide_Types.repl_state) :
  FStarC_Interactive_Ide_Types.repl_state=
  let uu___ = FStarC_Effect.op_Bang repl_stack in
  match uu___ with
  | [] -> failwith "(pop_repl) Too many pops"
  | (depth, (p, st'))::stack_tl ->
      let env =
        rollback_env
          (st.FStarC_Interactive_Ide_Types.repl_env).FStarC_TypeChecker_Env.solver
          msg depth in
      (FStarC_Effect.op_Colon_Equals repl_stack stack_tl;
       (let uu___3 =
          FStarC_Util.physical_equality env
            st'.FStarC_Interactive_Ide_Types.repl_env in
        FStarC_Common.runtime_assert uu___3 "Inconsistent stack state");
       if should_reset p
       then
         ((st'.FStarC_Interactive_Ide_Types.repl_env).FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.refresh
           FStar_Pervasives_Native.None
       else ();
       {
         FStarC_Interactive_Ide_Types.repl_line =
           (st'.FStarC_Interactive_Ide_Types.repl_line);
         FStarC_Interactive_Ide_Types.repl_column =
           (st'.FStarC_Interactive_Ide_Types.repl_column);
         FStarC_Interactive_Ide_Types.repl_fname =
           (st'.FStarC_Interactive_Ide_Types.repl_fname);
         FStarC_Interactive_Ide_Types.repl_deps_stack =
           (st'.FStarC_Interactive_Ide_Types.repl_deps_stack);
         FStarC_Interactive_Ide_Types.repl_curmod =
           (st'.FStarC_Interactive_Ide_Types.repl_curmod);
         FStarC_Interactive_Ide_Types.repl_env =
           (st'.FStarC_Interactive_Ide_Types.repl_env);
         FStarC_Interactive_Ide_Types.repl_stdin =
           (st'.FStarC_Interactive_Ide_Types.repl_stdin);
         FStarC_Interactive_Ide_Types.repl_names =
           (st'.FStarC_Interactive_Ide_Types.repl_names);
         FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
           (st.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
         FStarC_Interactive_Ide_Types.repl_lang =
           (st'.FStarC_Interactive_Ide_Types.repl_lang)
       })
let run_repl_task (repl_fname : Prims.string)
  (curmod : FStarC_Interactive_Ide_Types.optmod_t)
  (env : FStarC_TypeChecker_Env.env_t)
  (task : FStarC_Interactive_Ide_Types.repl_task)
  (lds : FStarC_Universal.lang_decls_t) :
  (FStarC_Interactive_Ide_Types.optmod_t * FStarC_TypeChecker_Env.env_t *
    FStarC_Universal.lang_decls_t)=
  match task with
  | FStarC_Interactive_Ide_Types.LDInterleaved (intf, impl) ->
      let uu___ =
        FStarC_Universal.load_file env
          (FStar_Pervasives_Native.Some
             (intf.FStarC_Interactive_Ide_Types.tf_fname))
          impl.FStarC_Interactive_Ide_Types.tf_fname in
      (curmod, uu___, [])
  | FStarC_Interactive_Ide_Types.LDSingle intf_or_impl ->
      let uu___ =
        FStarC_Universal.load_file env FStar_Pervasives_Native.None
          intf_or_impl.FStarC_Interactive_Ide_Types.tf_fname in
      (curmod, uu___, [])
  | FStarC_Interactive_Ide_Types.LDInterfaceOfCurrentFile intf ->
      let uu___ =
        FStarC_Universal.load_interface_decls env
          intf.FStarC_Interactive_Ide_Types.tf_fname in
      (curmod, uu___, [])
  | FStarC_Interactive_Ide_Types.PushFragment
      (frag, uu___, uu___1, filenames_to_load) ->
      let frag1 =
        match frag with
        | FStar_Pervasives.Inl frag2 -> FStar_Pervasives.Inl (frag2, lds)
        | FStar_Pervasives.Inr decl -> FStar_Pervasives.Inr decl in
      let is_interface = FStarC_Parser_Dep.is_interface repl_fname in
      let uu___2 =
        let uu___3 = FStarC_Parser_Dep.fly_deps_enabled () in
        if uu___3
        then
          FStarC_Universal.load_fly_deps_and_tc_one_fragment repl_fname
            is_interface curmod env frag1
        else
          (let uu___5 =
             FStarC_Universal.tc_one_fragment is_interface curmod env frag1 in
           match uu___5 with | (o, e, langs) -> (o, e, langs, [])) in
      (match uu___2 with
       | (o, e, langs, filenames) ->
           (add_filenames_to_push_fragment filenames; (o, e, langs)))
  | FStarC_Interactive_Ide_Types.Noop -> (curmod, env, [])
let query_of_ids (ids : FStarC_Ident.ident Prims.list) :
  FStarC_Interactive_CompletionTable.query=
  FStarC_List.map FStarC_Ident.string_of_id ids
let query_of_lid (lid : FStarC_Ident.lident) :
  FStarC_Interactive_CompletionTable.query=
  let uu___ =
    let uu___1 = FStarC_Ident.ns_of_lid lid in
    let uu___2 = let uu___3 = FStarC_Ident.ident_of_lid lid in [uu___3] in
    FStarC_List.op_At uu___1 uu___2 in
  query_of_ids uu___
let update_names_from_event (cur_mod_str : Prims.string)
  (table : FStarC_Interactive_CompletionTable.table)
  (evt : name_tracking_event) : FStarC_Interactive_CompletionTable.table=
  let is_cur_mod lid =
    let uu___ = FStarC_Ident.string_of_lid lid in uu___ = cur_mod_str in
  match evt with
  | NTAlias (host, id, included) ->
      let uu___ = is_cur_mod host in
      if uu___
      then
        let uu___1 = FStarC_Ident.string_of_id id in
        let uu___2 = query_of_lid included in
        FStarC_Interactive_CompletionTable.register_alias table uu___1 []
          uu___2
      else table
  | NTOpen (host, (included, kind, uu___)) ->
      let uu___1 = is_cur_mod host in
      if uu___1
      then
        let uu___2 = query_of_lid included in
        FStarC_Interactive_CompletionTable.register_open table
          (kind = FStarC_Syntax_Syntax.Open_module) [] uu___2
      else table
  | NTInclude (host, included) ->
      let uu___ =
        let uu___1 = is_cur_mod host in
        if uu___1 then [] else query_of_lid host in
      let uu___1 = query_of_lid included in
      FStarC_Interactive_CompletionTable.register_include table uu___ uu___1
  | NTBinding binding ->
      let lids =
        match binding with
        | FStar_Pervasives.Inl (FStarC_Syntax_Syntax.Binding_lid
            (lid, uu___)) -> [lid]
        | FStar_Pervasives.Inr (lids1, uu___) -> lids1
        | uu___ -> [] in
      FStarC_List.fold_left
        (fun tbl lid ->
           let ns_query =
             let uu___ =
               let uu___1 = FStarC_Ident.nsstr lid in uu___1 = cur_mod_str in
             if uu___
             then []
             else
               (let uu___2 = FStarC_Ident.ns_of_lid lid in
                query_of_ids uu___2) in
           let uu___ =
             let uu___1 = FStarC_Ident.ident_of_lid lid in
             FStarC_Ident.string_of_id uu___1 in
           FStarC_Interactive_CompletionTable.insert tbl ns_query uu___ lid)
        table lids
let commit_name_tracking'
  (cur_mod : FStarC_Syntax_Syntax.modul FStar_Pervasives_Native.option)
  (names : FStarC_Interactive_CompletionTable.table)
  (name_events : name_tracking_event Prims.list) :
  FStarC_Interactive_CompletionTable.table=
  let cur_mod_str =
    match cur_mod with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some md ->
        let uu___ = FStarC_Syntax_Syntax.mod_name md in
        FStarC_Ident.string_of_lid uu___ in
  let updater = update_names_from_event cur_mod_str in
  FStarC_List.fold_left updater names name_events
let commit_name_tracking (st : FStarC_Interactive_Ide_Types.repl_state)
  (name_events : name_tracking_event Prims.list) :
  FStarC_Interactive_Ide_Types.repl_state=
  let names =
    commit_name_tracking' st.FStarC_Interactive_Ide_Types.repl_curmod
      st.FStarC_Interactive_Ide_Types.repl_names name_events in
  {
    FStarC_Interactive_Ide_Types.repl_line =
      (st.FStarC_Interactive_Ide_Types.repl_line);
    FStarC_Interactive_Ide_Types.repl_column =
      (st.FStarC_Interactive_Ide_Types.repl_column);
    FStarC_Interactive_Ide_Types.repl_fname =
      (st.FStarC_Interactive_Ide_Types.repl_fname);
    FStarC_Interactive_Ide_Types.repl_deps_stack =
      (st.FStarC_Interactive_Ide_Types.repl_deps_stack);
    FStarC_Interactive_Ide_Types.repl_curmod =
      (st.FStarC_Interactive_Ide_Types.repl_curmod);
    FStarC_Interactive_Ide_Types.repl_env =
      (st.FStarC_Interactive_Ide_Types.repl_env);
    FStarC_Interactive_Ide_Types.repl_stdin =
      (st.FStarC_Interactive_Ide_Types.repl_stdin);
    FStarC_Interactive_Ide_Types.repl_names = names;
    FStarC_Interactive_Ide_Types.repl_buffered_input_queries =
      (st.FStarC_Interactive_Ide_Types.repl_buffered_input_queries);
    FStarC_Interactive_Ide_Types.repl_lang =
      (st.FStarC_Interactive_Ide_Types.repl_lang)
  }
let fresh_name_tracking_hooks (uu___ : unit) :
  (name_tracking_event Prims.list FStarC_Effect.ref *
    FStarC_Syntax_DsEnv.dsenv_hooks * FStarC_TypeChecker_Env.tcenv_hooks)=
  let events = FStarC_Effect.mk_ref [] in
  let push_event evt =
    let uu___1 = let uu___2 = FStarC_Effect.op_Bang events in evt :: uu___2 in
    FStarC_Effect.op_Colon_Equals events uu___1 in
  let uu___1 =
    FStarC_Syntax_DsEnv.mk_dsenv_hooks
      (fun dsenv op ->
         let uu___2 =
           let uu___3 =
             let uu___4 = FStarC_Syntax_DsEnv.current_module dsenv in
             (uu___4, op) in
           NTOpen uu___3 in
         push_event uu___2)
      (fun dsenv ns ->
         let uu___2 =
           let uu___3 =
             let uu___4 = FStarC_Syntax_DsEnv.current_module dsenv in
             (uu___4, ns) in
           NTInclude uu___3 in
         push_event uu___2)
      (fun dsenv x l ->
         let uu___2 =
           let uu___3 =
             let uu___4 = FStarC_Syntax_DsEnv.current_module dsenv in
             (uu___4, x, l) in
           NTAlias uu___3 in
         push_event uu___2) in
  (events, uu___1,
    {
      FStarC_TypeChecker_Env.tc_push_in_gamma_hook =
        (fun uu___2 s -> push_event (NTBinding s))
    })
let track_name_changes (env : FStarC_TypeChecker_Env.env_t) :
  (FStarC_TypeChecker_Env.env_t *
    (FStarC_TypeChecker_Env.env_t ->
       (FStarC_TypeChecker_Env.env_t * name_tracking_event Prims.list)))=
  let set_hooks dshooks tchooks env1 =
    let uu___ =
      FStarC_Universal.with_dsenv_of_tcenv env1
        (fun dsenv ->
           let uu___1 = FStarC_Syntax_DsEnv.set_ds_hooks dsenv dshooks in
           ((), uu___1)) in
    match uu___ with
    | ((), tcenv') -> FStarC_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
  let uu___ =
    let uu___1 =
      FStarC_Syntax_DsEnv.ds_hooks env.FStarC_TypeChecker_Env.dsenv in
    let uu___2 = FStarC_TypeChecker_Env.tc_hooks env in (uu___1, uu___2) in
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
                   let uu___5 = FStarC_Effect.op_Bang events in
                   FStarC_List.rev uu___5 in
                 (uu___3, uu___4)))))
let tf_of_fname (fname : Prims.string) :
  FStarC_Interactive_Ide_Types.timed_fname=
  let uu___ = FStarC_Parser_ParseIt.get_file_last_modification_time fname in
  {
    FStarC_Interactive_Ide_Types.tf_fname = fname;
    FStarC_Interactive_Ide_Types.tf_modtime = uu___
  }
let update_task_timestamps (uu___ : FStarC_Interactive_Ide_Types.repl_task) :
  FStarC_Interactive_Ide_Types.repl_task=
  match uu___ with
  | FStarC_Interactive_Ide_Types.LDInterleaved (intf, impl) ->
      let uu___1 =
        let uu___2 = tf_of_fname intf.FStarC_Interactive_Ide_Types.tf_fname in
        let uu___3 = tf_of_fname impl.FStarC_Interactive_Ide_Types.tf_fname in
        (uu___2, uu___3) in
      FStarC_Interactive_Ide_Types.LDInterleaved uu___1
  | FStarC_Interactive_Ide_Types.LDSingle intf_or_impl ->
      let uu___1 =
        tf_of_fname intf_or_impl.FStarC_Interactive_Ide_Types.tf_fname in
      FStarC_Interactive_Ide_Types.LDSingle uu___1
  | FStarC_Interactive_Ide_Types.LDInterfaceOfCurrentFile intf ->
      let uu___1 = tf_of_fname intf.FStarC_Interactive_Ide_Types.tf_fname in
      FStarC_Interactive_Ide_Types.LDInterfaceOfCurrentFile uu___1
  | other -> other
let add_module_completions (this_fname : Prims.string)
  (deps : Prims.string Prims.list)
  (table : FStarC_Interactive_CompletionTable.table) :
  FStarC_Interactive_CompletionTable.table=
  let capitalize str =
    if str = ""
    then str
    else
      (let first = FStarC_String.substring str Prims.int_zero Prims.int_one in
       let uu___1 =
         FStarC_String.substring str Prims.int_one
           ((FStarC_String.length str) - Prims.int_one) in
       Prims.strcat (FStarC_String.uppercase first) uu___1) in
  let mods = FStarC_Parser_Dep.build_inclusion_candidates_list () in
  let loaded_mods_set =
    let uu___ = FStarC_PSMap.empty () in
    FStarC_List.fold_left
      (fun acc dep ->
         let uu___1 = FStarC_Parser_Dep.lowercase_module_name dep in
         FStarC_PSMap.add acc uu___1 true) uu___ deps in
  let loaded modname =
    FStarC_PSMap.find_default loaded_mods_set modname false in
  let this_mod_key = FStarC_Parser_Dep.lowercase_module_name this_fname in
  FStarC_List.fold_left
    (fun table1 uu___ ->
       match uu___ with
       | (modname, mod_path) ->
           let mod_key = FStarC_String.lowercase modname in
           if this_mod_key = mod_key
           then table1
           else
             (let ns_query =
                let uu___2 = capitalize modname in
                FStarC_Util.split uu___2 "." in
              let uu___2 = loaded mod_key in
              FStarC_Interactive_CompletionTable.register_module_path table1
                uu___2 mod_path ns_query)) table (FStarC_List.rev mods)
