open Prims
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      (FStar_JsonHelper.repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun msg ->
      let uu____40 = FStar_TypeChecker_Tc.snapshot_context env msg in
      match uu____40 with
      | (ctx_depth, env1) ->
          let uu____84 = FStar_Options.snapshot () in
          (match uu____84 with
           | (opt_depth, ()) -> ((ctx_depth, opt_depth), env1))
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver1 ->
    fun msg ->
      fun uu____130 ->
        match uu____130 with
        | (ctx_depth, opt_depth) ->
            let env =
              FStar_TypeChecker_Tc.rollback_context solver1 msg
                (FStar_Pervasives_Native.Some ctx_depth) in
            (FStar_Options.rollback (FStar_Pervasives_Native.Some opt_depth);
             env)
type push_kind =
  | SyntaxCheck 
  | LaxCheck 
  | FullCheck 
let (uu___is_SyntaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | SyntaxCheck -> true | uu____197 -> false
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | LaxCheck -> true | uu____208 -> false
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | FullCheck -> true | uu____219 -> false
let (set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun check_kind ->
      let uu___26_232 = env in
      let uu____233 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___26_232.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___26_232.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___26_232.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___26_232.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___26_232.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___26_232.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___26_232.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___26_232.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___26_232.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___26_232.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___26_232.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___26_232.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___26_232.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___26_232.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___26_232.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___26_232.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___26_232.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___26_232.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___26_232.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___26_232.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___26_232.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___26_232.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___26_232.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___26_232.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___26_232.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___26_232.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___26_232.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___26_232.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___26_232.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___26_232.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___26_232.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___26_232.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___26_232.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___26_232.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___26_232.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___26_232.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___26_232.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___26_232.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___26_232.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___26_232.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____233;
        FStar_TypeChecker_Env.nbe = (uu___26_232.FStar_TypeChecker_Env.nbe)
      }
let with_captured_errors' :
  'Auu____243 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____243 FStar_Pervasives_Native.option)
          -> 'Auu____243 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        try
          (fun uu___32_273 ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____279 -> f env)) ()
        with
        | FStar_All.Failure msg ->
            let msg1 =
              Prims.op_Hat "ASSERTION FAILURE: "
                (Prims.op_Hat msg
                   (Prims.op_Hat "\n"
                      (Prims.op_Hat "F* may be in an inconsistent state.\n"
                         (Prims.op_Hat
                            "Please file a bug report, ideally with a "
                            "minimized version of the program that triggered the error.")))) in
            ((let uu____297 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.log_issue uu____297
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e, msg, r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e, msg) ->
            ((let uu____327 =
                let uu____337 =
                  let uu____345 = FStar_TypeChecker_Env.get_range env in
                  (e, msg, uu____345) in
                [uu____337] in
              FStar_TypeChecker_Err.add_errors env uu____327);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop -> FStar_Pervasives_Native.None
let with_captured_errors :
  'Auu____370 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____370 FStar_Pervasives_Native.option)
          -> 'Auu____370 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        let uu____397 = FStar_Options.trace_error () in
        if uu____397
        then f env
        else with_captured_errors' env sigint_handler f
let (t0 : FStar_Util.time) = FStar_Util.now ()
let (tf_of_fname : Prims.string -> FStar_JsonHelper.timed_fname) =
  fun fname ->
    let uu____413 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname in
    {
      FStar_JsonHelper.tf_fname = fname;
      FStar_JsonHelper.tf_modtime = uu____413
    }
let (dummy_tf_of_fname : Prims.string -> FStar_JsonHelper.timed_fname) =
  fun fname ->
    { FStar_JsonHelper.tf_fname = fname; FStar_JsonHelper.tf_modtime = t0 }
let (string_of_timed_fname : FStar_JsonHelper.timed_fname -> Prims.string) =
  fun uu____428 ->
    match uu____428 with
    | { FStar_JsonHelper.tf_fname = fname;
        FStar_JsonHelper.tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____438 = FStar_Util.string_of_time modtime in
           FStar_Util.format2 "{ %s; %s }" fname uu____438)
type push_query =
  {
  push_kind: push_kind ;
  push_code: Prims.string ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool }
let (__proj__Mkpush_query__item__push_kind : push_query -> push_kind) =
  fun projectee ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_kind
let (__proj__Mkpush_query__item__push_code : push_query -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_code
let (__proj__Mkpush_query__item__push_line : push_query -> Prims.int) =
  fun projectee ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_line
let (__proj__Mkpush_query__item__push_column : push_query -> Prims.int) =
  fun projectee ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_column
let (__proj__Mkpush_query__item__push_peek_only : push_query -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_peek_only
type env_t = FStar_TypeChecker_Env.env
let (repl_current_qid :
  Prims.string FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (repl_stack : FStar_JsonHelper.repl_stack_t FStar_ST.ref) =
  FStar_Util.mk_ref []
let (pop_repl :
  Prims.string -> FStar_JsonHelper.repl_state -> FStar_JsonHelper.repl_state)
  =
  fun msg ->
    fun st ->
      let uu____587 = FStar_ST.op_Bang repl_stack in
      match uu____587 with
      | [] -> failwith "Too many pops"
      | (depth, (uu____617, st'))::stack_tl ->
          let env =
            rollback_env
              (st.FStar_JsonHelper.repl_env).FStar_TypeChecker_Env.solver msg
              depth in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____664 =
              FStar_Util.physical_equality env st'.FStar_JsonHelper.repl_env in
            FStar_Common.runtime_assert uu____664 "Inconsistent stack state");
           st')
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
          let uu____690 = snapshot_env st.FStar_JsonHelper.repl_env msg in
          match uu____690 with
          | (depth, env) ->
              ((let uu____698 =
                  let uu____699 = FStar_ST.op_Bang repl_stack in
                  (depth, (task, st)) :: uu____699 in
                FStar_ST.op_Colon_Equals repl_stack uu____698);
               (let uu___101_760 = st in
                let uu____761 = set_check_kind env push_kind in
                {
                  FStar_JsonHelper.repl_line =
                    (uu___101_760.FStar_JsonHelper.repl_line);
                  FStar_JsonHelper.repl_column =
                    (uu___101_760.FStar_JsonHelper.repl_column);
                  FStar_JsonHelper.repl_fname =
                    (uu___101_760.FStar_JsonHelper.repl_fname);
                  FStar_JsonHelper.repl_deps_stack =
                    (uu___101_760.FStar_JsonHelper.repl_deps_stack);
                  FStar_JsonHelper.repl_curmod =
                    (uu___101_760.FStar_JsonHelper.repl_curmod);
                  FStar_JsonHelper.repl_env = uu____761;
                  FStar_JsonHelper.repl_stdin =
                    (uu___101_760.FStar_JsonHelper.repl_stdin);
                  FStar_JsonHelper.repl_names =
                    (uu___101_760.FStar_JsonHelper.repl_names)
                }))
let (nothing_left_to_pop : FStar_JsonHelper.repl_state -> Prims.bool) =
  fun st ->
    let uu____769 =
      let uu____770 = FStar_ST.op_Bang repl_stack in
      FStar_List.length uu____770 in
    uu____769 = (FStar_List.length st.FStar_JsonHelper.repl_deps_stack)
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of (FStar_Syntax_Syntax.binding,
  FStar_TypeChecker_Env.sig_binding) FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTAlias _0 -> true | uu____870 -> false
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee -> match projectee with | NTAlias _0 -> _0
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTOpen _0 -> true | uu____911 -> false
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee -> match projectee with | NTOpen _0 -> _0
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTInclude _0 -> true | uu____946 -> false
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee -> match projectee with | NTInclude _0 -> _0
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTBinding _0 -> true | uu____981 -> false
let (__proj__NTBinding__item___0 :
  name_tracking_event ->
    (FStar_Syntax_Syntax.binding, FStar_TypeChecker_Env.sig_binding)
      FStar_Util.either)
  = fun projectee -> match projectee with | NTBinding _0 -> _0
let (query_of_ids :
  FStar_Ident.ident Prims.list -> FStar_Interactive_CompletionTable.query) =
  fun ids -> FStar_List.map FStar_Ident.text_of_id ids
let (query_of_lid :
  FStar_Ident.lident -> FStar_Interactive_CompletionTable.query) =
  fun lid ->
    query_of_ids
      (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident])
let (update_names_from_event :
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod_str ->
    fun table ->
      fun evt ->
        let is_cur_mod lid = lid.FStar_Ident.str = cur_mod_str in
        match evt with
        | NTAlias (host, id1, included) ->
            if is_cur_mod host
            then
              let uu____1049 = FStar_Ident.text_of_id id1 in
              let uu____1051 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                uu____1049 [] uu____1051
            else table
        | NTOpen (host, (included, kind)) ->
            if is_cur_mod host
            then
              let uu____1059 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____1059
            else table
        | NTInclude (host, included) ->
            let uu____1065 =
              if is_cur_mod host then [] else query_of_lid host in
            let uu____1070 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____1065 uu____1070
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid, uu____1082)) -> [lid]
              | FStar_Util.Inr (lids, uu____1100) -> lids
              | uu____1105 -> [] in
            FStar_List.fold_left
              (fun tbl ->
                 fun lid ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns in
                   let uu____1122 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____1122 lid) table lids
let (commit_name_tracking' :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event Prims.list ->
        FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod ->
    fun names1 ->
      fun name_events ->
        let cur_mod_str =
          match cur_mod with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some md ->
              let uu____1153 = FStar_Syntax_Syntax.mod_name md in
              uu____1153.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let (commit_name_tracking :
  FStar_JsonHelper.repl_state ->
    name_tracking_event Prims.list -> FStar_JsonHelper.repl_state)
  =
  fun st ->
    fun name_events ->
      let names1 =
        commit_name_tracking' st.FStar_JsonHelper.repl_curmod
          st.FStar_JsonHelper.repl_names name_events in
      let uu___161_1179 = st in
      {
        FStar_JsonHelper.repl_line =
          (uu___161_1179.FStar_JsonHelper.repl_line);
        FStar_JsonHelper.repl_column =
          (uu___161_1179.FStar_JsonHelper.repl_column);
        FStar_JsonHelper.repl_fname =
          (uu___161_1179.FStar_JsonHelper.repl_fname);
        FStar_JsonHelper.repl_deps_stack =
          (uu___161_1179.FStar_JsonHelper.repl_deps_stack);
        FStar_JsonHelper.repl_curmod =
          (uu___161_1179.FStar_JsonHelper.repl_curmod);
        FStar_JsonHelper.repl_env = (uu___161_1179.FStar_JsonHelper.repl_env);
        FStar_JsonHelper.repl_stdin =
          (uu___161_1179.FStar_JsonHelper.repl_stdin);
        FStar_JsonHelper.repl_names = names1
      }
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____1195 ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____1209 =
        let uu____1212 = FStar_ST.op_Bang events in evt :: uu____1212 in
      FStar_ST.op_Colon_Equals events uu____1209 in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1 ->
             fun op ->
               let uu____1273 =
                 let uu____1274 =
                   let uu____1279 = FStar_Syntax_DsEnv.current_module dsenv1 in
                   (uu____1279, op) in
                 NTOpen uu____1274 in
               push_event uu____1273);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1 ->
             fun ns ->
               let uu____1285 =
                 let uu____1286 =
                   let uu____1291 = FStar_Syntax_DsEnv.current_module dsenv1 in
                   (uu____1291, ns) in
                 NTInclude uu____1286 in
               push_event uu____1285);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1 ->
             fun x ->
               fun l ->
                 let uu____1299 =
                   let uu____1300 =
                     let uu____1307 =
                       FStar_Syntax_DsEnv.current_module dsenv1 in
                     (uu____1307, x, l) in
                   NTAlias uu____1300 in
                 push_event uu____1299)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1312 -> fun s -> push_event (NTBinding s))
      })
let (track_name_changes :
  env_t -> (env_t * (env_t -> (env_t * name_tracking_event Prims.list)))) =
  fun env ->
    let set_hooks dshooks tchooks env1 =
      let uu____1366 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv1 ->
             let uu____1374 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks in
             ((), uu____1374)) in
      match uu____1366 with
      | ((), tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu____1376 =
      let uu____1381 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu____1382 = FStar_TypeChecker_Env.tc_hooks env in
      (uu____1381, uu____1382) in
    match uu____1376 with
    | (old_dshooks, old_tchooks) ->
        let uu____1398 = fresh_name_tracking_hooks () in
        (match uu____1398 with
         | (events, new_dshooks, new_tchooks) ->
             let uu____1433 = set_hooks new_dshooks new_tchooks env in
             (uu____1433,
               ((fun env1 ->
                   let uu____1447 = set_hooks old_dshooks old_tchooks env1 in
                   let uu____1448 =
                     let uu____1451 = FStar_ST.op_Bang events in
                     FStar_List.rev uu____1451 in
                   (uu____1447, uu____1448)))))
let (string_of_repl_task : FStar_JsonHelper.repl_task -> Prims.string) =
  fun uu___0_1485 ->
    match uu___0_1485 with
    | FStar_JsonHelper.LDInterleaved (intf, impl) ->
        let uu____1489 = string_of_timed_fname intf in
        let uu____1491 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1489 uu____1491
    | FStar_JsonHelper.LDSingle intf_or_impl ->
        let uu____1495 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____1495
    | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu____1499 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1499
    | FStar_JsonHelper.PushFragment frag ->
        FStar_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
    | FStar_JsonHelper.Noop -> "Noop {}"
let (tc_one :
  env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> FStar_TypeChecker_Env.env_t)
  =
  fun env ->
    fun intf_opt ->
      fun modf ->
        let uu____1529 =
          let uu____1534 =
            let uu____1535 =
              let uu____1541 = FStar_TypeChecker_Env.dep_graph env in
              FStar_Parser_Dep.parsing_data_of uu____1541 in
            FStar_All.pipe_right modf uu____1535 in
          FStar_Universal.tc_one_file_for_ide env intf_opt modf uu____1534 in
        match uu____1529 with | (uu____1543, env1) -> env1
let (run_repl_task :
  FStar_JsonHelper.optmod_t ->
    env_t ->
      FStar_JsonHelper.repl_task -> (FStar_JsonHelper.optmod_t * env_t))
  =
  fun curmod ->
    fun env ->
      fun task ->
        match task with
        | FStar_JsonHelper.LDInterleaved (intf, impl) ->
            let uu____1571 =
              tc_one env
                (FStar_Pervasives_Native.Some
                   (intf.FStar_JsonHelper.tf_fname))
                impl.FStar_JsonHelper.tf_fname in
            (curmod, uu____1571)
        | FStar_JsonHelper.LDSingle intf_or_impl ->
            let uu____1574 =
              tc_one env FStar_Pervasives_Native.None
                intf_or_impl.FStar_JsonHelper.tf_fname in
            (curmod, uu____1574)
        | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
            let uu____1577 =
              FStar_Universal.load_interface_decls env
                intf.FStar_JsonHelper.tf_fname in
            (curmod, uu____1577)
        | FStar_JsonHelper.PushFragment frag ->
            FStar_Universal.tc_one_fragment curmod env frag
        | FStar_JsonHelper.Noop -> (curmod, env)
let (repl_ld_tasks_of_deps :
  Prims.string Prims.list ->
    FStar_JsonHelper.repl_task Prims.list ->
      FStar_JsonHelper.repl_task Prims.list)
  =
  fun deps ->
    fun final_tasks ->
      let wrap = dummy_tf_of_fname in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____1643 = aux deps' final_tasks1 in
            (FStar_JsonHelper.LDInterleaved ((wrap intf), (wrap impl))) ::
              uu____1643
        | intf_or_impl::deps' ->
            let uu____1653 = aux deps' final_tasks1 in
            (FStar_JsonHelper.LDSingle (wrap intf_or_impl)) :: uu____1653
        | [] -> final_tasks1 in
      aux deps final_tasks
let (deps_and_repl_ld_tasks_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * FStar_JsonHelper.repl_task Prims.list *
      FStar_Parser_Dep.deps))
  =
  fun filename ->
    let get_mod_name fname = FStar_Parser_Dep.lowercase_module_name fname in
    let our_mod_name = get_mod_name filename in
    let has_our_mod_name f =
      let uu____1707 = get_mod_name f in uu____1707 = our_mod_name in
    let uu____1710 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_CheckedFiles.load_parsing_data_from_cache in
    match uu____1710 with
    | (deps, dep_graph1) ->
        let uu____1739 = FStar_List.partition has_our_mod_name deps in
        (match uu____1739 with
         | (same_name, real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____1789 =
                       let uu____1791 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu____1791 in
                     if uu____1789
                     then
                       let uu____1794 =
                         let uu____1800 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.Fatal_MissingInterface, uu____1800) in
                       FStar_Errors.raise_err uu____1794
                     else ());
                    (let uu____1807 =
                       let uu____1809 =
                         FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu____1809 in
                     if uu____1807
                     then
                       let uu____1812 =
                         let uu____1818 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____1818) in
                       FStar_Errors.raise_err uu____1812
                     else ());
                    [FStar_JsonHelper.LDInterfaceOfCurrentFile
                       (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____1828 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu____1839 =
                       let uu____1845 =
                         FStar_Util.format message [our_mod_name; mods_str] in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____1845) in
                     FStar_Errors.raise_err uu____1839);
                    []) in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
             (real_deps, tasks, dep_graph1))
let (update_task_timestamps :
  FStar_JsonHelper.repl_task -> FStar_JsonHelper.repl_task) =
  fun uu___1_1864 ->
    match uu___1_1864 with
    | FStar_JsonHelper.LDInterleaved (intf, impl) ->
        let uu____1867 =
          let uu____1872 = tf_of_fname intf.FStar_JsonHelper.tf_fname in
          let uu____1873 = tf_of_fname impl.FStar_JsonHelper.tf_fname in
          (uu____1872, uu____1873) in
        FStar_JsonHelper.LDInterleaved uu____1867
    | FStar_JsonHelper.LDSingle intf_or_impl ->
        let uu____1875 = tf_of_fname intf_or_impl.FStar_JsonHelper.tf_fname in
        FStar_JsonHelper.LDSingle uu____1875
    | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
        let uu____1877 = tf_of_fname intf.FStar_JsonHelper.tf_fname in
        FStar_JsonHelper.LDInterfaceOfCurrentFile uu____1877
    | other -> other
let (run_repl_transaction :
  FStar_JsonHelper.repl_state ->
    push_kind ->
      Prims.bool ->
        FStar_JsonHelper.repl_task ->
          (Prims.bool * FStar_JsonHelper.repl_state))
  =
  fun st ->
    fun push_kind ->
      fun must_rollback ->
        fun task ->
          let st1 = push_repl "run_repl_transaction" push_kind task st in
          let uu____1909 = track_name_changes st1.FStar_JsonHelper.repl_env in
          match uu____1909 with
          | (env, finish_name_tracking) ->
              let check_success uu____1954 =
                (let uu____1957 = FStar_Errors.get_err_count () in
                 uu____1957 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback) in
              let uu____1961 =
                let uu____1969 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1 ->
                       let uu____1983 =
                         run_repl_task st1.FStar_JsonHelper.repl_curmod env1
                           task in
                       FStar_All.pipe_left
                         (fun _2002 -> FStar_Pervasives_Native.Some _2002)
                         uu____1983) in
                match uu____1969 with
                | FStar_Pervasives_Native.Some (curmod, env1) when
                    check_success () -> (curmod, env1, true)
                | uu____2018 ->
                    ((st1.FStar_JsonHelper.repl_curmod), env, false) in
              (match uu____1961 with
               | (curmod, env1, success) ->
                   let uu____2037 = finish_name_tracking env1 in
                   (match uu____2037 with
                    | (env2, name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___301_2058 = st1 in
                              {
                                FStar_JsonHelper.repl_line =
                                  (uu___301_2058.FStar_JsonHelper.repl_line);
                                FStar_JsonHelper.repl_column =
                                  (uu___301_2058.FStar_JsonHelper.repl_column);
                                FStar_JsonHelper.repl_fname =
                                  (uu___301_2058.FStar_JsonHelper.repl_fname);
                                FStar_JsonHelper.repl_deps_stack =
                                  (uu___301_2058.FStar_JsonHelper.repl_deps_stack);
                                FStar_JsonHelper.repl_curmod = curmod;
                                FStar_JsonHelper.repl_env = env2;
                                FStar_JsonHelper.repl_stdin =
                                  (uu___301_2058.FStar_JsonHelper.repl_stdin);
                                FStar_JsonHelper.repl_names =
                                  (uu___301_2058.FStar_JsonHelper.repl_names)
                              } in
                            commit_name_tracking st2 name_events
                          else pop_repl "run_repl_transaction" st1 in
                        (success, st2)))
let (run_repl_ld_transactions :
  FStar_JsonHelper.repl_state ->
    FStar_JsonHelper.repl_task Prims.list ->
      (FStar_JsonHelper.repl_task -> unit) ->
        (FStar_JsonHelper.repl_state, FStar_JsonHelper.repl_state)
          FStar_Util.either)
  =
  fun st ->
    fun tasks ->
      fun progress_callback ->
        let debug1 verb task =
          let uu____2105 = FStar_Options.debug_any () in
          if uu____2105
          then
            let uu____2108 = string_of_repl_task task in
            FStar_Util.print2 "%s %s" verb uu____2108
          else () in
        let rec revert_many st1 uu___2_2133 =
          match uu___2_2133 with
          | [] -> st1
          | (_id, (task, _st'))::entries ->
              (debug1 "Reverting" task;
               (let st' = pop_repl "run_repl_ls_transactions" st1 in
                let dep_graph1 =
                  FStar_TypeChecker_Env.dep_graph
                    st1.FStar_JsonHelper.repl_env in
                let st'1 =
                  let uu___327_2186 = st' in
                  let uu____2187 =
                    FStar_TypeChecker_Env.set_dep_graph
                      st'.FStar_JsonHelper.repl_env dep_graph1 in
                  {
                    FStar_JsonHelper.repl_line =
                      (uu___327_2186.FStar_JsonHelper.repl_line);
                    FStar_JsonHelper.repl_column =
                      (uu___327_2186.FStar_JsonHelper.repl_column);
                    FStar_JsonHelper.repl_fname =
                      (uu___327_2186.FStar_JsonHelper.repl_fname);
                    FStar_JsonHelper.repl_deps_stack =
                      (uu___327_2186.FStar_JsonHelper.repl_deps_stack);
                    FStar_JsonHelper.repl_curmod =
                      (uu___327_2186.FStar_JsonHelper.repl_curmod);
                    FStar_JsonHelper.repl_env = uu____2187;
                    FStar_JsonHelper.repl_stdin =
                      (uu___327_2186.FStar_JsonHelper.repl_stdin);
                    FStar_JsonHelper.repl_names =
                      (uu___327_2186.FStar_JsonHelper.repl_names)
                  } in
                revert_many st'1 entries)) in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([], []) -> FStar_Util.Inl st1
          | (task::tasks2, []) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____2240 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu____2240 (fun a1 -> ()));
               (let timestamped_task = update_task_timestamps task in
                let push_kind =
                  let uu____2244 = FStar_Options.lax () in
                  if uu____2244 then LaxCheck else FullCheck in
                let uu____2249 =
                  run_repl_transaction st1 push_kind false timestamped_task in
                match uu____2249 with
                | (success, st2) ->
                    if success
                    then
                      let uu____2269 =
                        let uu___352_2270 = st2 in
                        let uu____2271 = FStar_ST.op_Bang repl_stack in
                        {
                          FStar_JsonHelper.repl_line =
                            (uu___352_2270.FStar_JsonHelper.repl_line);
                          FStar_JsonHelper.repl_column =
                            (uu___352_2270.FStar_JsonHelper.repl_column);
                          FStar_JsonHelper.repl_fname =
                            (uu___352_2270.FStar_JsonHelper.repl_fname);
                          FStar_JsonHelper.repl_deps_stack = uu____2271;
                          FStar_JsonHelper.repl_curmod =
                            (uu___352_2270.FStar_JsonHelper.repl_curmod);
                          FStar_JsonHelper.repl_env =
                            (uu___352_2270.FStar_JsonHelper.repl_env);
                          FStar_JsonHelper.repl_stdin =
                            (uu___352_2270.FStar_JsonHelper.repl_stdin);
                          FStar_JsonHelper.repl_names =
                            (uu___352_2270.FStar_JsonHelper.repl_names)
                        } in
                      aux uu____2269 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2, prev::previous1) when
              let uu____2315 = update_task_timestamps task in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____2315
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2, previous1) ->
              let uu____2332 = revert_many st1 previous1 in
              aux uu____2332 tasks2 [] in
        aux st tasks (FStar_List.rev st.FStar_JsonHelper.repl_deps_stack)
let (js_pushkind : FStar_Util.json -> push_kind) =
  fun s ->
    let uu____2347 = FStar_JsonHelper.js_str s in
    match uu____2347 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____2352 -> FStar_JsonHelper.js_fail "push_kind" s
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s ->
    let uu____2361 = FStar_JsonHelper.js_str s in
    match uu____2361 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____2369 -> FStar_JsonHelper.js_fail "reduction rule" s
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKCode -> true | uu____2398 -> false
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKOption _0 -> true | uu____2411 -> false
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKOption _0 -> _0
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____2439 -> false
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee -> match projectee with | CKModuleOrNamespace _0 -> _0
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2477 = FStar_JsonHelper.js_str k1 in
        (match uu____2477 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____2505 ->
             FStar_JsonHelper.js_fail
               "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
type lookup_context =
  | LKSymbolOnly 
  | LKModule 
  | LKOption 
  | LKCode 
let (uu___is_LKSymbolOnly : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKSymbolOnly -> true | uu____2517 -> false
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKModule -> true | uu____2528 -> false
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKOption -> true | uu____2539 -> false
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKCode -> true | uu____2550 -> false
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2563 = FStar_JsonHelper.js_str k1 in
        (match uu____2563 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____2573 ->
             FStar_JsonHelper.js_fail
               "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
type position = (Prims.string * Prims.int * Prims.int)
type query' =
  | Exit 
  | DescribeProtocol 
  | DescribeRepl 
  | Segment of Prims.string 
  | Pop 
  | Push of push_query 
  | VfsAdd of (Prims.string FStar_Pervasives_Native.option * Prims.string) 
  | AutoComplete of (Prims.string * completion_context) 
  | Lookup of (Prims.string * lookup_context * position
  FStar_Pervasives_Native.option * Prims.string Prims.list) 
  | Compute of (Prims.string * FStar_TypeChecker_Env.step Prims.list
  FStar_Pervasives_Native.option) 
  | Search of Prims.string 
  | GenericError of Prims.string 
  | ProtocolViolation of Prims.string 
and query = {
  qq: query' ;
  qid: Prims.string }
let (uu___is_Exit : query' -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu____2690 -> false
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeProtocol -> true | uu____2701 -> false
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeRepl -> true | uu____2712 -> false
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Segment _0 -> true | uu____2725 -> false
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Segment _0 -> _0
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu____2746 -> false
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Push _0 -> true | uu____2758 -> false
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | VfsAdd _0 -> true | uu____2785 -> false
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee -> match projectee with | VfsAdd _0 -> _0
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | AutoComplete _0 -> true | uu____2833 -> false
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee -> match projectee with | AutoComplete _0 -> _0
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Lookup _0 -> true | uu____2881 -> false
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee -> match projectee with | Lookup _0 -> _0
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Compute _0 -> true | uu____2951 -> false
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Compute _0 -> _0
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Search _0 -> true | uu____2998 -> false
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Search _0 -> _0
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | GenericError _0 -> true | uu____3021 -> false
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | GenericError _0 -> _0
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | ProtocolViolation _0 -> true | uu____3044 -> false
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | ProtocolViolation _0 -> _0
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___3_3082 ->
    match uu___3_3082 with
    | Exit -> false
    | DescribeProtocol -> false
    | DescribeRepl -> false
    | Segment uu____3087 -> false
    | Pop -> false
    | Push
        { push_kind = uu____3091; push_code = uu____3092;
          push_line = uu____3093; push_column = uu____3094;
          push_peek_only = false;_}
        -> false
    | VfsAdd uu____3100 -> false
    | GenericError uu____3110 -> false
    | ProtocolViolation uu____3113 -> false
    | Push uu____3116 -> true
    | AutoComplete uu____3118 -> true
    | Lookup uu____3125 -> true
    | Compute uu____3141 -> true
    | Search uu____3152 -> true
let (interactive_protocol_vernum : Prims.int) = (Prims.parse_int "2")
let (interactive_protocol_features : Prims.string Prims.list) =
  ["autocomplete";
  "autocomplete/context";
  "compute";
  "compute/reify";
  "compute/pure-subterms";
  "describe-protocol";
  "describe-repl";
  "exit";
  "lookup";
  "lookup/context";
  "lookup/documentation";
  "lookup/definition";
  "peek";
  "pop";
  "push";
  "search";
  "segment";
  "vfs-add";
  "tactic-ranges";
  "interrupt";
  "progress"]
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let (uu___is_QueryOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryOK -> true | uu____3214 -> false
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryNOK -> true | uu____3225 -> false
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with
    | QueryViolatesProtocol -> true
    | uu____3236 -> false
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____3258 =
          let uu____3259 =
            let uu____3261 = FStar_JsonHelper.json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____3261 in
          ProtocolViolation uu____3259 in
        { qq = uu____3258; qid }
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json ->
    let assoc1 errloc key a =
      let uu____3304 = FStar_JsonHelper.try_assoc key a in
      match uu____3304 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____3308 =
            let uu____3309 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            FStar_JsonHelper.InvalidQuery uu____3309 in
          FStar_Exn.raise uu____3308 in
    let request = FStar_All.pipe_right json FStar_JsonHelper.js_assoc in
    let qid =
      let uu____3329 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____3329 FStar_JsonHelper.js_str in
    try
      (fun uu___465_3339 ->
         match () with
         | () ->
             let query =
               let uu____3342 = assoc1 "query" "query" request in
               FStar_All.pipe_right uu____3342 FStar_JsonHelper.js_str in
             let args =
               let uu____3354 = assoc1 "query" "args" request in
               FStar_All.pipe_right uu____3354 FStar_JsonHelper.js_assoc in
             let arg1 k = assoc1 "[args]" k args in
             let try_arg k =
               let uu____3383 = FStar_JsonHelper.try_assoc k args in
               match uu____3383 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull) ->
                   FStar_Pervasives_Native.None
               | other -> other in
             let uu____3391 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____3397 =
                     let uu____3399 = arg1 "code" in
                     FStar_All.pipe_right uu____3399 FStar_JsonHelper.js_str in
                   Segment uu____3397
               | "peek" ->
                   let uu____3403 =
                     let uu____3404 =
                       let uu____3405 = arg1 "kind" in
                       FStar_All.pipe_right uu____3405 js_pushkind in
                     let uu____3407 =
                       let uu____3409 = arg1 "code" in
                       FStar_All.pipe_right uu____3409
                         FStar_JsonHelper.js_str in
                     let uu____3412 =
                       let uu____3414 = arg1 "line" in
                       FStar_All.pipe_right uu____3414
                         FStar_JsonHelper.js_int in
                     let uu____3417 =
                       let uu____3419 = arg1 "column" in
                       FStar_All.pipe_right uu____3419
                         FStar_JsonHelper.js_int in
                     {
                       push_kind = uu____3404;
                       push_code = uu____3407;
                       push_line = uu____3412;
                       push_column = uu____3417;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____3403
               | "push" ->
                   let uu____3425 =
                     let uu____3426 =
                       let uu____3427 = arg1 "kind" in
                       FStar_All.pipe_right uu____3427 js_pushkind in
                     let uu____3429 =
                       let uu____3431 = arg1 "code" in
                       FStar_All.pipe_right uu____3431
                         FStar_JsonHelper.js_str in
                     let uu____3434 =
                       let uu____3436 = arg1 "line" in
                       FStar_All.pipe_right uu____3436
                         FStar_JsonHelper.js_int in
                     let uu____3439 =
                       let uu____3441 = arg1 "column" in
                       FStar_All.pipe_right uu____3441
                         FStar_JsonHelper.js_int in
                     {
                       push_kind = uu____3426;
                       push_code = uu____3429;
                       push_line = uu____3434;
                       push_column = uu____3439;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____3425
               | "autocomplete" ->
                   let uu____3447 =
                     let uu____3453 =
                       let uu____3455 = arg1 "partial-symbol" in
                       FStar_All.pipe_right uu____3455
                         FStar_JsonHelper.js_str in
                     let uu____3458 =
                       let uu____3459 = try_arg "context" in
                       FStar_All.pipe_right uu____3459
                         js_optional_completion_context in
                     (uu____3453, uu____3458) in
                   AutoComplete uu____3447
               | "lookup" ->
                   let uu____3467 =
                     let uu____3482 =
                       let uu____3484 = arg1 "symbol" in
                       FStar_All.pipe_right uu____3484
                         FStar_JsonHelper.js_str in
                     let uu____3487 =
                       let uu____3488 = try_arg "context" in
                       FStar_All.pipe_right uu____3488
                         js_optional_lookup_context in
                     let uu____3494 =
                       let uu____3497 =
                         let uu____3507 = try_arg "location" in
                         FStar_All.pipe_right uu____3507
                           (FStar_Util.map_option FStar_JsonHelper.js_assoc) in
                       FStar_All.pipe_right uu____3497
                         (FStar_Util.map_option
                            (fun loc ->
                               let uu____3568 =
                                 let uu____3570 =
                                   assoc1 "[location]" "filename" loc in
                                 FStar_All.pipe_right uu____3570
                                   FStar_JsonHelper.js_str in
                               let uu____3574 =
                                 let uu____3576 =
                                   assoc1 "[location]" "line" loc in
                                 FStar_All.pipe_right uu____3576
                                   FStar_JsonHelper.js_int in
                               let uu____3580 =
                                 let uu____3582 =
                                   assoc1 "[location]" "column" loc in
                                 FStar_All.pipe_right uu____3582
                                   FStar_JsonHelper.js_int in
                               (uu____3568, uu____3574, uu____3580))) in
                     let uu____3589 =
                       let uu____3593 = arg1 "requested-info" in
                       FStar_All.pipe_right uu____3593
                         (FStar_JsonHelper.js_list FStar_JsonHelper.js_str) in
                     (uu____3482, uu____3487, uu____3494, uu____3589) in
                   Lookup uu____3467
               | "compute" ->
                   let uu____3606 =
                     let uu____3616 =
                       let uu____3618 = arg1 "term" in
                       FStar_All.pipe_right uu____3618
                         FStar_JsonHelper.js_str in
                     let uu____3621 =
                       let uu____3626 = try_arg "rules" in
                       FStar_All.pipe_right uu____3626
                         (FStar_Util.map_option
                            (FStar_JsonHelper.js_list js_reductionrule)) in
                     (uu____3616, uu____3621) in
                   Compute uu____3606
               | "search" ->
                   let uu____3644 =
                     let uu____3646 = arg1 "terms" in
                     FStar_All.pipe_right uu____3646 FStar_JsonHelper.js_str in
                   Search uu____3644
               | "vfs-add" ->
                   let uu____3650 =
                     let uu____3659 =
                       let uu____3663 = try_arg "filename" in
                       FStar_All.pipe_right uu____3663
                         (FStar_Util.map_option FStar_JsonHelper.js_str) in
                     let uu____3673 =
                       let uu____3675 = arg1 "contents" in
                       FStar_All.pipe_right uu____3675
                         FStar_JsonHelper.js_str in
                     (uu____3659, uu____3673) in
                   VfsAdd uu____3650
               | uu____3682 ->
                   let uu____3684 =
                     FStar_Util.format1 "Unknown query '%s'" query in
                   ProtocolViolation uu____3684 in
             { qq = uu____3391; qid }) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure qid expected got
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query ->
    try
      (fun uu___500_3703 ->
         match () with | () -> unpack_interactive_query js_query) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid = "?" }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure "?" expected got
let (parse_interactive_query : Prims.string -> query) =
  fun query_str ->
    let uu____3723 = FStar_Util.json_of_string query_str in
    match uu____3723 with
    | FStar_Pervasives_Native.None ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream ->
    let uu____3735 = FStar_Util.read_line stream in
    match uu____3735 with
    | FStar_Pervasives_Native.None -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
let json_of_opt :
  'Auu____3751 .
    ('Auu____3751 -> FStar_Util.json) ->
      'Auu____3751 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a ->
    fun opt_a ->
      let uu____3771 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____3771
let (json_of_issue_level : FStar_Errors.issue_level -> FStar_Util.json) =
  fun i ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented -> "not-implemented"
       | FStar_Errors.EInfo -> "info"
       | FStar_Errors.EWarning -> "warning"
       | FStar_Errors.EError -> "error")
let (json_of_issue : FStar_Errors.issue -> FStar_Util.json) =
  fun issue ->
    let uu____3791 =
      let uu____3799 =
        let uu____3807 =
          let uu____3815 =
            let uu____3821 =
              let uu____3822 =
                let uu____3825 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____3831 = FStar_Range.json_of_use_range r in
                      [uu____3831] in
                let uu____3832 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____3838 = FStar_Range.def_range r in
                      let uu____3839 = FStar_Range.use_range r in
                      uu____3838 <> uu____3839 ->
                      let uu____3840 = FStar_Range.json_of_def_range r in
                      [uu____3840]
                  | uu____3841 -> [] in
                FStar_List.append uu____3825 uu____3832 in
              FStar_Util.JsonList uu____3822 in
            ("ranges", uu____3821) in
          [uu____3815] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____3807 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____3799 in
    FStar_Util.JsonAssoc uu____3791
let (alist_of_symbol_lookup_result :
  FStar_QueryHelper.sl_reponse -> (Prims.string * FStar_Util.json) Prims.list)
  =
  fun lr ->
    let uu____3883 =
      let uu____3891 =
        let uu____3897 =
          json_of_opt FStar_Range.json_of_def_range
            lr.FStar_QueryHelper.slr_def_range in
        ("defined-at", uu____3897) in
      let uu____3900 =
        let uu____3908 =
          let uu____3914 =
            json_of_opt (fun _3916 -> FStar_Util.JsonStr _3916)
              lr.FStar_QueryHelper.slr_typ in
          ("type", uu____3914) in
        let uu____3919 =
          let uu____3927 =
            let uu____3933 =
              json_of_opt (fun _3935 -> FStar_Util.JsonStr _3935)
                lr.FStar_QueryHelper.slr_doc in
            ("documentation", uu____3933) in
          let uu____3938 =
            let uu____3946 =
              let uu____3952 =
                json_of_opt (fun _3954 -> FStar_Util.JsonStr _3954)
                  lr.FStar_QueryHelper.slr_def in
              ("definition", uu____3952) in
            [uu____3946] in
          uu____3927 :: uu____3938 in
        uu____3908 :: uu____3919 in
      uu____3891 :: uu____3900 in
    ("name", (FStar_Util.JsonStr (lr.FStar_QueryHelper.slr_name))) ::
      uu____3883
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3999 =
      FStar_List.map (fun _4003 -> FStar_Util.JsonStr _4003)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _4006 -> FStar_Util.JsonList _4006) uu____3999 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptSet -> true | uu____4035 -> false
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReset -> true | uu____4046 -> false
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReadOnly -> true | uu____4057 -> false
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___4_4065 ->
    match uu___4_4065 with
    | OptSet -> ""
    | OptReset -> "requires #reset-options"
    | OptReadOnly -> "read-only"
type fstar_option =
  {
  opt_name: Prims.string ;
  opt_sig: Prims.string ;
  opt_value: FStar_Options.option_val ;
  opt_default: FStar_Options.option_val ;
  opt_type: FStar_Options.opt_type ;
  opt_snippets: Prims.string Prims.list ;
  opt_documentation: Prims.string FStar_Pervasives_Native.option ;
  opt_permission_level: fstar_option_permission_level }
let (__proj__Mkfstar_option__item__opt_name : fstar_option -> Prims.string) =
  fun projectee ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_name
let (__proj__Mkfstar_option__item__opt_sig : fstar_option -> Prims.string) =
  fun projectee ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_sig
let (__proj__Mkfstar_option__item__opt_value :
  fstar_option -> FStar_Options.option_val) =
  fun projectee ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_value
let (__proj__Mkfstar_option__item__opt_default :
  fstar_option -> FStar_Options.option_val) =
  fun projectee ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_default
let (__proj__Mkfstar_option__item__opt_type :
  fstar_option -> FStar_Options.opt_type) =
  fun projectee ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_type
let (__proj__Mkfstar_option__item__opt_snippets :
  fstar_option -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_snippets
let (__proj__Mkfstar_option__item__opt_documentation :
  fstar_option -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_documentation
let (__proj__Mkfstar_option__item__opt_permission_level :
  fstar_option -> fstar_option_permission_level) =
  fun projectee ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_permission_level
let rec (kind_of_fstar_option_type : FStar_Options.opt_type -> Prims.string)
  =
  fun uu___5_4316 ->
    match uu___5_4316 with
    | FStar_Options.Const uu____4318 -> "flag"
    | FStar_Options.IntStr uu____4320 -> "int"
    | FStar_Options.BoolStr -> "bool"
    | FStar_Options.PathStr uu____4324 -> "path"
    | FStar_Options.SimpleStr uu____4327 -> "string"
    | FStar_Options.EnumStr uu____4330 -> "enum"
    | FStar_Options.OpenEnumStr uu____4335 -> "open enum"
    | FStar_Options.PostProcessed (uu____4345, typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____4355, typ) ->
        kind_of_fstar_option_type typ
let rec (snippets_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string Prims.list) =
  fun name ->
    fun typ ->
      let mk_field field_name =
        Prims.op_Hat "${" (Prims.op_Hat field_name "}") in
      let mk_snippet name1 argstring =
        Prims.op_Hat "--"
          (Prims.op_Hat name1
             (if argstring <> "" then Prims.op_Hat " " argstring else "")) in
      let rec arg_snippets_of_type typ1 =
        match typ1 with
        | FStar_Options.Const uu____4427 -> [""]
        | FStar_Options.BoolStr -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs, desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____4465, elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____4475, elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____4483 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____4483
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___6_4494 ->
    match uu___6_4494 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____4506 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____4506
    | FStar_Options.Unset -> FStar_Util.JsonNull
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt ->
    let uu____4522 =
      let uu____4530 =
        let uu____4538 =
          let uu____4544 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____4544) in
        let uu____4547 =
          let uu____4555 =
            let uu____4561 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____4561) in
          let uu____4564 =
            let uu____4572 =
              let uu____4578 =
                json_of_opt (fun _4580 -> FStar_Util.JsonStr _4580)
                  opt.opt_documentation in
              ("documentation", uu____4578) in
            let uu____4583 =
              let uu____4591 =
                let uu____4597 =
                  let uu____4598 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____4598 in
                ("type", uu____4597) in
              [uu____4591;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____4572 :: uu____4583 in
          uu____4555 :: uu____4564 in
        uu____4538 :: uu____4547 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____4530 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____4522
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt ->
    let uu____4654 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____4654
let (json_of_response :
  Prims.string -> query_status -> FStar_Util.json -> FStar_Util.json) =
  fun qid ->
    fun status ->
      fun response ->
        let qid1 = FStar_Util.JsonStr qid in
        let status1 =
          match status with
          | QueryOK -> FStar_Util.JsonStr "success"
          | QueryNOK -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol -> FStar_Util.JsonStr "protocol-violation" in
        FStar_Util.JsonAssoc
          [("kind", (FStar_Util.JsonStr "response"));
          ("query-id", qid1);
          ("status", status1);
          ("response", response)]
let (write_response :
  Prims.string -> query_status -> FStar_Util.json -> unit) =
  fun qid ->
    fun status ->
      fun response ->
        FStar_JsonHelper.write_json (json_of_response qid status response)
let (json_of_message : Prims.string -> FStar_Util.json -> FStar_Util.json) =
  fun level ->
    fun js_contents ->
      let uu____4750 =
        let uu____4758 =
          let uu____4766 =
            let uu____4772 =
              let uu____4773 = FStar_ST.op_Bang repl_current_qid in
              json_of_opt (fun _4803 -> FStar_Util.JsonStr _4803) uu____4773 in
            ("query-id", uu____4772) in
          [uu____4766;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)] in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____4758 in
      FStar_Util.JsonAssoc uu____4750
let forward_message :
  'Auu____4847 .
    (FStar_Util.json -> 'Auu____4847) ->
      Prims.string -> FStar_Util.json -> 'Auu____4847
  =
  fun callback ->
    fun level ->
      fun contents ->
        let uu____4870 = json_of_message level contents in
        callback uu____4870
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____4874 =
      FStar_List.map (fun _4878 -> FStar_Util.JsonStr _4878)
        interactive_protocol_features in
    FStar_Util.JsonList uu____4874 in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
let (write_hello : unit -> unit) =
  fun uu____4892 -> FStar_JsonHelper.write_json json_of_hello
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name ->
    fun typ ->
      let flag = Prims.op_Hat "--" name in
      let uu____4910 = FStar_Options.desc_of_opt_type typ in
      match uu____4910 with
      | FStar_Pervasives_Native.None -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____4926 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____4961 ->
            match uu____4961 with
            | (_shortname, name, typ, doc1) ->
                let uu____4985 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____4985
                  (FStar_Util.map_option
                     (fun default_value ->
                        let uu____4997 = sig_of_fstar_option name typ in
                        let uu____4999 = snippets_of_fstar_option name typ in
                        let uu____5003 =
                          let uu____5004 = FStar_Options.settable name in
                          if uu____5004
                          then OptSet
                          else
                            (let uu____5009 = FStar_Options.resettable name in
                             if uu____5009 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____4997;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____4999;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____5003
                        })))) in
  FStar_All.pipe_right uu____4926
    (FStar_List.sortWith
       (fun o1 ->
          fun o2 ->
            FStar_String.compare (FStar_String.lowercase o1.opt_name)
              (FStar_String.lowercase o2.opt_name)))
let (fstar_options_map_cache : fstar_option FStar_Util.smap) =
  let cache = FStar_Util.smap_create (Prims.parse_int "50") in
  FStar_List.iter (fun opt -> FStar_Util.smap_add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache
let (update_option : fstar_option -> fstar_option) =
  fun opt ->
    let uu___672_5048 = opt in
    let uu____5049 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___672_5048.opt_name);
      opt_sig = (uu___672_5048.opt_sig);
      opt_value = uu____5049;
      opt_default = (uu___672_5048.opt_default);
      opt_type = (uu___672_5048.opt_type);
      opt_snippets = (uu___672_5048.opt_snippets);
      opt_documentation = (uu___672_5048.opt_documentation);
      opt_permission_level = (uu___672_5048.opt_permission_level)
    }
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1 ->
    let uu____5065 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____5065
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____5092 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____5092)
    else ("", opt_name)
let (json_of_repl_state : FStar_JsonHelper.repl_state -> FStar_Util.json) =
  fun st ->
    let filenames uu____5123 =
      match uu____5123 with
      | (uu____5135, (task, uu____5137)) ->
          (match task with
           | FStar_JsonHelper.LDInterleaved (intf, impl) ->
               [intf.FStar_JsonHelper.tf_fname;
               impl.FStar_JsonHelper.tf_fname]
           | FStar_JsonHelper.LDSingle intf_or_impl ->
               [intf_or_impl.FStar_JsonHelper.tf_fname]
           | FStar_JsonHelper.LDInterfaceOfCurrentFile intf ->
               [intf.FStar_JsonHelper.tf_fname]
           | uu____5156 -> []) in
    let uu____5158 =
      let uu____5166 =
        let uu____5172 =
          let uu____5173 =
            let uu____5176 =
              FStar_List.concatMap filenames
                st.FStar_JsonHelper.repl_deps_stack in
            FStar_List.map (fun _5190 -> FStar_Util.JsonStr _5190) uu____5176 in
          FStar_Util.JsonList uu____5173 in
        ("loaded-dependencies", uu____5172) in
      let uu____5193 =
        let uu____5201 =
          let uu____5207 =
            let uu____5208 =
              let uu____5211 = current_fstar_options (fun uu____5216 -> true) in
              FStar_List.map json_of_fstar_option uu____5211 in
            FStar_Util.JsonList uu____5208 in
          ("options", uu____5207) in
        [uu____5201] in
      uu____5166 :: uu____5193 in
    FStar_Util.JsonAssoc uu____5158
let run_exit :
  'Auu____5242 'Auu____5243 .
    'Auu____5242 ->
      ((query_status * FStar_Util.json) * ('Auu____5243, Prims.int)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol :
  'Auu____5280 'Auu____5281 .
    'Auu____5280 ->
      ((query_status * FStar_Util.json) * ('Auu____5280, 'Auu____5281)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl :
  'Auu____5312 .
    FStar_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
        'Auu____5312) FStar_Util.either)
  =
  fun st ->
    let uu____5330 =
      let uu____5335 = json_of_repl_state st in (QueryOK, uu____5335) in
    (uu____5330, (FStar_Util.Inl st))
let run_protocol_violation :
  'Auu____5353 'Auu____5354 .
    'Auu____5353 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____5353, 'Auu____5354)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error :
  'Auu____5396 'Auu____5397 .
    'Auu____5396 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____5396, 'Auu____5397)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____5437 ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment :
  'Auu____5449 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____5449) FStar_Util.either)
  =
  fun st ->
    fun code ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
          FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
        } in
      let collect_decls uu____5484 =
        let uu____5485 = FStar_Parser_Driver.parse_fragment frag in
        match uu____5485 with
        | FStar_Parser_Driver.Empty -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____5491, decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____5497, decls, uu____5499)) -> decls in
      let uu____5506 =
        with_captured_errors st.FStar_JsonHelper.repl_env
          FStar_Util.sigint_ignore
          (fun uu____5515 ->
             let uu____5516 = collect_decls () in
             FStar_All.pipe_left
               (fun _5527 -> FStar_Pervasives_Native.Some _5527) uu____5516) in
      match uu____5506 with
      | FStar_Pervasives_Native.None ->
          let errors =
            let uu____5545 = collect_errors () in
            FStar_All.pipe_right uu____5545 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____5571 =
              let uu____5579 =
                let uu____5585 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu____5585) in
              [uu____5579] in
            FStar_Util.JsonAssoc uu____5571 in
          let js_decls =
            let uu____5599 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left (fun _5604 -> FStar_Util.JsonList _5604)
              uu____5599 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add :
  'Auu____5634 .
    FStar_JsonHelper.repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____5634) FStar_Util.either)
  =
  fun st ->
    fun opt_fname ->
      fun contents ->
        let fname = FStar_Util.dflt st.FStar_JsonHelper.repl_fname opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop :
  'Auu____5687 .
    FStar_JsonHelper.repl_state ->
      ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
        'Auu____5687) FStar_Util.either)
  =
  fun st ->
    let uu____5705 = nothing_left_to_pop st in
    if uu____5705
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let st' = pop_repl "pop_query" st in
       ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))
let (write_progress :
  Prims.string FStar_Pervasives_Native.option ->
    (Prims.string * FStar_Util.json) Prims.list -> unit)
  =
  fun stage ->
    fun contents_alist ->
      let stage1 =
        match stage with
        | FStar_Pervasives_Native.Some s -> FStar_Util.JsonStr s
        | FStar_Pervasives_Native.None -> FStar_Util.JsonNull in
      let js_contents = ("stage", stage1) :: contents_alist in
      let uu____5792 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents) in
      FStar_JsonHelper.write_json uu____5792
let (write_repl_ld_task_progress : FStar_JsonHelper.repl_task -> unit) =
  fun task ->
    match task with
    | FStar_JsonHelper.LDInterleaved (uu____5800, tf) ->
        let modname =
          FStar_Parser_Dep.module_name_of_file tf.FStar_JsonHelper.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | FStar_JsonHelper.LDSingle tf ->
        let modname =
          FStar_Parser_Dep.module_name_of_file tf.FStar_JsonHelper.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | FStar_JsonHelper.LDInterfaceOfCurrentFile tf ->
        let modname =
          FStar_Parser_Dep.module_name_of_file tf.FStar_JsonHelper.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | uu____5852 -> ()
let (load_deps :
  FStar_JsonHelper.repl_state ->
    ((FStar_JsonHelper.repl_state * Prims.string Prims.list),
      FStar_JsonHelper.repl_state) FStar_Util.either)
  =
  fun st ->
    let uu____5870 =
      with_captured_errors st.FStar_JsonHelper.repl_env
        FStar_Util.sigint_ignore
        (fun _env ->
           let uu____5898 =
             deps_and_repl_ld_tasks_of_our_file
               st.FStar_JsonHelper.repl_fname in
           FStar_All.pipe_left
             (fun _5945 -> FStar_Pervasives_Native.Some _5945) uu____5898) in
    match uu____5870 with
    | FStar_Pervasives_Native.None -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) ->
        let st1 =
          let uu___762_6000 = st in
          let uu____6001 =
            FStar_TypeChecker_Env.set_dep_graph st.FStar_JsonHelper.repl_env
              dep_graph1 in
          {
            FStar_JsonHelper.repl_line =
              (uu___762_6000.FStar_JsonHelper.repl_line);
            FStar_JsonHelper.repl_column =
              (uu___762_6000.FStar_JsonHelper.repl_column);
            FStar_JsonHelper.repl_fname =
              (uu___762_6000.FStar_JsonHelper.repl_fname);
            FStar_JsonHelper.repl_deps_stack =
              (uu___762_6000.FStar_JsonHelper.repl_deps_stack);
            FStar_JsonHelper.repl_curmod =
              (uu___762_6000.FStar_JsonHelper.repl_curmod);
            FStar_JsonHelper.repl_env = uu____6001;
            FStar_JsonHelper.repl_stdin =
              (uu___762_6000.FStar_JsonHelper.repl_stdin);
            FStar_JsonHelper.repl_names =
              (uu___762_6000.FStar_JsonHelper.repl_names)
          } in
        let uu____6002 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress in
        (match uu____6002 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue ->
    let uu___772_6057 = issue in
    let uu____6058 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____6058;
      FStar_Errors.issue_level = (uu___772_6057.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___772_6057.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___772_6057.FStar_Errors.issue_number)
    }
let run_push_without_deps :
  'Auu____6068 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____6068) FStar_Util.either)
  =
  fun st ->
    fun query ->
      let set_nosynth_flag st1 flag =
        let uu___779_6104 = st1 in
        {
          FStar_JsonHelper.repl_line =
            (uu___779_6104.FStar_JsonHelper.repl_line);
          FStar_JsonHelper.repl_column =
            (uu___779_6104.FStar_JsonHelper.repl_column);
          FStar_JsonHelper.repl_fname =
            (uu___779_6104.FStar_JsonHelper.repl_fname);
          FStar_JsonHelper.repl_deps_stack =
            (uu___779_6104.FStar_JsonHelper.repl_deps_stack);
          FStar_JsonHelper.repl_curmod =
            (uu___779_6104.FStar_JsonHelper.repl_curmod);
          FStar_JsonHelper.repl_env =
            (let uu___781_6106 = st1.FStar_JsonHelper.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___781_6106.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___781_6106.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___781_6106.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___781_6106.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___781_6106.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___781_6106.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___781_6106.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___781_6106.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___781_6106.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___781_6106.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___781_6106.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___781_6106.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___781_6106.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___781_6106.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___781_6106.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___781_6106.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___781_6106.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___781_6106.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___781_6106.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___781_6106.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___781_6106.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___781_6106.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___781_6106.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___781_6106.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___781_6106.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___781_6106.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___781_6106.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___781_6106.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___781_6106.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___781_6106.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___781_6106.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___781_6106.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___781_6106.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___781_6106.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___781_6106.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___781_6106.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___781_6106.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___781_6106.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___781_6106.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___781_6106.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___781_6106.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___781_6106.FStar_TypeChecker_Env.nbe)
             });
          FStar_JsonHelper.repl_stdin =
            (uu___779_6104.FStar_JsonHelper.repl_stdin);
          FStar_JsonHelper.repl_names =
            (uu___779_6104.FStar_JsonHelper.repl_names)
        } in
      let uu____6107 = query in
      match uu____6107 with
      | { push_kind; push_code = text; push_line = line;
          push_column = column; push_peek_only = peek_only;_} ->
          let frag =
            {
              FStar_Parser_ParseIt.frag_text = text;
              FStar_Parser_ParseIt.frag_line = line;
              FStar_Parser_ParseIt.frag_col = column
            } in
          (FStar_TypeChecker_Env.toggle_id_info st.FStar_JsonHelper.repl_env
             true;
           (let st1 = set_nosynth_flag st peek_only in
            let uu____6133 =
              run_repl_transaction st1 push_kind peek_only
                (FStar_JsonHelper.PushFragment frag) in
            match uu____6133 with
            | (success, st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____6162 =
                    let uu____6165 = collect_errors () in
                    FStar_All.pipe_right uu____6165
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____6162 in
                let st4 =
                  if success
                  then
                    let uu___800_6174 = st3 in
                    {
                      FStar_JsonHelper.repl_line = line;
                      FStar_JsonHelper.repl_column = column;
                      FStar_JsonHelper.repl_fname =
                        (uu___800_6174.FStar_JsonHelper.repl_fname);
                      FStar_JsonHelper.repl_deps_stack =
                        (uu___800_6174.FStar_JsonHelper.repl_deps_stack);
                      FStar_JsonHelper.repl_curmod =
                        (uu___800_6174.FStar_JsonHelper.repl_curmod);
                      FStar_JsonHelper.repl_env =
                        (uu___800_6174.FStar_JsonHelper.repl_env);
                      FStar_JsonHelper.repl_stdin =
                        (uu___800_6174.FStar_JsonHelper.repl_stdin);
                      FStar_JsonHelper.repl_names =
                        (uu___800_6174.FStar_JsonHelper.repl_names)
                    }
                  else st3 in
                ((status, json_errors), (FStar_Util.Inl st4))))
let (capitalize : Prims.string -> Prims.string) =
  fun str ->
    if str = ""
    then str
    else
      (let first =
         FStar_String.substring str (Prims.parse_int "0")
           (Prims.parse_int "1") in
       let uu____6204 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1")) in
       Prims.op_Hat (FStar_String.uppercase first) uu____6204)
let (add_module_completions :
  Prims.string ->
    Prims.string Prims.list ->
      FStar_Interactive_CompletionTable.table ->
        FStar_Interactive_CompletionTable.table)
  =
  fun this_fname ->
    fun deps ->
      fun table ->
        let mods = FStar_Parser_Dep.build_inclusion_candidates_list () in
        let loaded_mods_set =
          let uu____6245 = FStar_Util.psmap_empty () in
          let uu____6250 =
            let uu____6254 = FStar_Options.prims () in uu____6254 :: deps in
          FStar_List.fold_left
            (fun acc ->
               fun dep1 ->
                 let uu____6270 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____6270 true) uu____6245
            uu____6250 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1 ->
             fun uu____6299 ->
               match uu____6299 with
               | (modname, mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____6322 = capitalize modname in
                        FStar_Util.split uu____6322 "." in
                      let uu____6325 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____6325 mod_path ns_query)) table
          (FStar_List.rev mods)
let run_push_with_deps :
  'Auu____6340 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____6340) FStar_Util.either)
  =
  fun st ->
    fun query ->
      (let uu____6364 = FStar_Options.debug_any () in
       if uu____6364
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.FStar_JsonHelper.repl_env false;
      (let uu____6372 = load_deps st in
       match uu____6372 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____6407 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____6407 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1, deps) ->
           ((let uu____6441 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____6441 (fun a2 -> ()));
            (let names1 =
               add_module_completions st1.FStar_JsonHelper.repl_fname deps
                 st1.FStar_JsonHelper.repl_names in
             run_push_without_deps
               (let uu___838_6445 = st1 in
                {
                  FStar_JsonHelper.repl_line =
                    (uu___838_6445.FStar_JsonHelper.repl_line);
                  FStar_JsonHelper.repl_column =
                    (uu___838_6445.FStar_JsonHelper.repl_column);
                  FStar_JsonHelper.repl_fname =
                    (uu___838_6445.FStar_JsonHelper.repl_fname);
                  FStar_JsonHelper.repl_deps_stack =
                    (uu___838_6445.FStar_JsonHelper.repl_deps_stack);
                  FStar_JsonHelper.repl_curmod =
                    (uu___838_6445.FStar_JsonHelper.repl_curmod);
                  FStar_JsonHelper.repl_env =
                    (uu___838_6445.FStar_JsonHelper.repl_env);
                  FStar_JsonHelper.repl_stdin =
                    (uu___838_6445.FStar_JsonHelper.repl_stdin);
                  FStar_JsonHelper.repl_names = names1
                }) query)))
let run_push :
  'Auu____6453 .
    FStar_JsonHelper.repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____6453) FStar_Util.either)
  =
  fun st ->
    fun query ->
      let uu____6476 = nothing_left_to_pop st in
      if uu____6476
      then run_push_with_deps st query
      else run_push_without_deps st query
let (run_symbol_lookup :
  FStar_JsonHelper.repl_state ->
    Prims.string ->
      FStar_QueryHelper.position FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,
            (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
            FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let uu____6543 =
            FStar_QueryHelper.symlookup st.FStar_JsonHelper.repl_env symbol
              pos_opt requested_info in
          match uu____6543 with
          | FStar_Pervasives_Native.None -> FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some result ->
              let uu____6578 =
                let uu____6591 = alist_of_symbol_lookup_result result in
                ("symbol", uu____6591) in
              FStar_Util.Inr uu____6578
let (run_option_lookup :
  Prims.string ->
    (Prims.string,
      (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
      FStar_Util.either)
  =
  fun opt_name ->
    let uu____6646 = trim_option_name opt_name in
    match uu____6646 with
    | (uu____6670, trimmed_name) ->
        let uu____6676 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____6676 with
         | FStar_Pervasives_Native.None ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____6711 =
               let uu____6724 =
                 let uu____6732 = update_option opt in
                 alist_of_fstar_option uu____6732 in
               ("option", uu____6724) in
             FStar_Util.Inr uu____6711)
let (run_module_lookup :
  FStar_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string,
        (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
        FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      let query = FStar_Util.split symbol "." in
      let uu____6790 =
        FStar_Interactive_CompletionTable.find_module_or_ns
          st.FStar_JsonHelper.repl_names query in
      match uu____6790 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____6825 =
            let uu____6838 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____6838) in
          FStar_Util.Inr uu____6825
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____6869 =
            let uu____6882 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____6882) in
          FStar_Util.Inr uu____6869
let (run_code_lookup :
  FStar_JsonHelper.repl_state ->
    Prims.string ->
      FStar_QueryHelper.position FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,
            (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
            FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let uu____6962 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____6962 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____7036 ->
              let uu____7051 = run_module_lookup st symbol in
              (match uu____7051 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
let (run_lookup' :
  FStar_JsonHelper.repl_state ->
    Prims.string ->
      lookup_context ->
        FStar_QueryHelper.position FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            (Prims.string,
              (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
              FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun context ->
        fun pos_opt ->
          fun requested_info ->
            match context with
            | LKSymbolOnly ->
                run_symbol_lookup st symbol pos_opt requested_info
            | LKModule -> run_module_lookup st symbol
            | LKOption -> run_option_lookup symbol
            | LKCode -> run_code_lookup st symbol pos_opt requested_info
let run_lookup :
  'Auu____7239 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        lookup_context ->
          FStar_QueryHelper.position FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) *
                (FStar_JsonHelper.repl_state, 'Auu____7239)
                FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun context ->
        fun pos_opt ->
          fun requested_info ->
            let uu____7289 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____7289 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind, info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let code_autocomplete_mod_filter :
  'Auu____7393 .
    ('Auu____7393 * FStar_Interactive_CompletionTable.mod_symbol) ->
      ('Auu____7393 * FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___7_7408 ->
    match uu___7_7408 with
    | (uu____7413, FStar_Interactive_CompletionTable.Namespace uu____7414) ->
        FStar_Pervasives_Native.None
    | (uu____7419, FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____7420;
         FStar_Interactive_CompletionTable.mod_path = uu____7421;
         FStar_Interactive_CompletionTable.mod_loaded = true;_})
        -> FStar_Pervasives_Native.None
    | (pth, FStar_Interactive_CompletionTable.Module md) ->
        let uu____7431 =
          let uu____7436 =
            let uu____7437 =
              let uu___915_7438 = md in
              let uu____7439 =
                let uu____7441 =
                  FStar_Interactive_CompletionTable.mod_name md in
                Prims.op_Hat uu____7441 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____7439;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___915_7438.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___915_7438.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____7437 in
          (pth, uu____7436) in
        FStar_Pervasives_Native.Some uu____7431
let run_code_autocomplete :
  'Auu____7455 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____7455) FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      let needle = FStar_Util.split search_term "." in
      let mods_and_nss =
        FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
          st.FStar_JsonHelper.repl_names needle code_autocomplete_mod_filter in
      let lids =
        FStar_Interactive_CompletionTable.autocomplete_lid
          st.FStar_JsonHelper.repl_names needle in
      let json =
        FStar_List.map
          FStar_Interactive_CompletionTable.json_of_completion_result
          (FStar_List.append lids mods_and_nss) in
      ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let run_module_autocomplete :
  'Auu____7517 'Auu____7518 'Auu____7519 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        'Auu____7517 ->
          'Auu____7518 ->
            ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
              'Auu____7519) FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun modules1 ->
        fun namespaces ->
          let needle = FStar_Util.split search_term "." in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.FStar_JsonHelper.repl_names needle
              (fun _7566 -> FStar_Pervasives_Native.Some _7566) in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let (candidates_of_fstar_option :
  Prims.int ->
    Prims.bool ->
      fstar_option ->
        FStar_Interactive_CompletionTable.completion_result Prims.list)
  =
  fun match_len ->
    fun is_reset ->
      fun opt ->
        let uu____7600 =
          match opt.opt_permission_level with
          | OptSet -> (true, "")
          | OptReset -> (is_reset, "#reset-only")
          | OptReadOnly -> (false, "read-only") in
        match uu____7600 with
        | (may_set, explanation) ->
            let opt_type = kind_of_fstar_option_type opt.opt_type in
            let annot =
              if may_set
              then opt_type
              else
                Prims.op_Hat "("
                  (Prims.op_Hat explanation
                     (Prims.op_Hat " " (Prims.op_Hat opt_type ")"))) in
            FStar_All.pipe_right opt.opt_snippets
              (FStar_List.map
                 (fun snippet ->
                    {
                      FStar_Interactive_CompletionTable.completion_match_length
                        = match_len;
                      FStar_Interactive_CompletionTable.completion_candidate
                        = snippet;
                      FStar_Interactive_CompletionTable.completion_annotation
                        = annot
                    }))
let run_option_autocomplete :
  'Auu____7663 'Auu____7664 .
    'Auu____7663 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____7663, 'Auu____7664)
            FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun is_reset ->
        let uu____7696 = trim_option_name search_term in
        match uu____7696 with
        | ("--", trimmed_name) ->
            let matcher opt =
              FStar_Util.starts_with opt.opt_name trimmed_name in
            let options = current_fstar_options matcher in
            let match_len = FStar_String.length search_term in
            let collect_candidates =
              candidates_of_fstar_option match_len is_reset in
            let results = FStar_List.concatMap collect_candidates options in
            let json =
              FStar_List.map
                FStar_Interactive_CompletionTable.json_of_completion_result
                results in
            ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
        | (uu____7752, uu____7753) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete :
  'Auu____7776 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____7776) FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun context ->
        match context with
        | CKCode -> run_code_autocomplete st search_term
        | CKOption is_reset ->
            run_option_autocomplete st search_term is_reset
        | CKModuleOrNamespace (modules1, namespaces) ->
            run_module_autocomplete st search_term modules1 namespaces
let run_and_rewind :
  'Auu____7827 'Auu____7828 .
    FStar_JsonHelper.repl_state ->
      'Auu____7827 ->
        (FStar_JsonHelper.repl_state -> 'Auu____7827) ->
          ('Auu____7827 * (FStar_JsonHelper.repl_state, 'Auu____7828)
            FStar_Util.either)
  =
  fun st ->
    fun sigint_default ->
      fun task ->
        let st1 =
          push_repl "run_and_rewind" FullCheck FStar_JsonHelper.Noop st in
        let results =
          try
            (fun uu___974_7869 ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____7880 ->
                        let uu____7881 = task st1 in
                        FStar_All.pipe_left
                          (fun _7886 -> FStar_Util.Inl _7886) uu____7881)) ()
          with | FStar_Util.SigInt -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e in
        let st2 = pop_repl "run_and_rewind" st1 in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
let run_with_parsed_and_tc_term :
  'Auu____7935 'Auu____7936 'Auu____7937 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        'Auu____7935 ->
          'Auu____7936 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) *
                (FStar_JsonHelper.repl_state, 'Auu____7937)
                FStar_Util.either)
  =
  fun st ->
    fun term ->
      fun line ->
        fun column ->
          fun continuation ->
            let dummy_let_fragment term1 =
              let dummy_decl =
                FStar_Util.format1 "let __compute_dummy__ = (%s)" term1 in
              {
                FStar_Parser_ParseIt.frag_text = dummy_decl;
                FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
                FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
              } in
            let find_let_body ses =
              match ses with
              | {
                  FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                    ((uu____8038,
                      { FStar_Syntax_Syntax.lbname = uu____8039;
                        FStar_Syntax_Syntax.lbunivs = univs1;
                        FStar_Syntax_Syntax.lbtyp = uu____8041;
                        FStar_Syntax_Syntax.lbeff = uu____8042;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu____8044;
                        FStar_Syntax_Syntax.lbpos = uu____8045;_}::[]),
                     uu____8046);
                  FStar_Syntax_Syntax.sigrng = uu____8047;
                  FStar_Syntax_Syntax.sigquals = uu____8048;
                  FStar_Syntax_Syntax.sigmeta = uu____8049;
                  FStar_Syntax_Syntax.sigattrs = uu____8050;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____8089 -> FStar_Pervasives_Native.None in
            let parse1 frag =
              let uu____8110 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu____8110 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls, uu____8116) ->
                  FStar_Pervasives_Native.Some decls
              | uu____8137 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu____8155 =
                let uu____8160 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu____8160 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu____8155 in
            let typecheck tcenv decls =
              let uu____8182 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu____8182 with | (ses, uu____8196, uu____8197) -> ses in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1 ->
                 let tcenv = st1.FStar_JsonHelper.repl_env in
                 let frag = dummy_let_fragment term in
                 let uu____8218 = parse1 frag in
                 match uu____8218 with
                 | FStar_Pervasives_Native.None ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____8244 =
                       let decls1 = desugar tcenv decls in
                       let ses = typecheck tcenv decls1 in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1, def) ->
                           let uu____8280 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def in
                           (match uu____8280 with
                            | (univs2, def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2 in
                                continuation tcenv1 def1) in
                     let uu____8292 = FStar_Options.trace_error () in
                     if uu____8292
                     then aux ()
                     else
                       (try
                          (fun uu___1057_8306 -> match () with | () -> aux ())
                            ()
                        with
                        | uu___1056_8315 ->
                            let uu____8320 =
                              FStar_Errors.issue_of_exn uu___1056_8315 in
                            (match uu____8320 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____8328 =
                                   let uu____8329 =
                                     FStar_Errors.format_issue issue in
                                   FStar_Util.JsonStr uu____8329 in
                                 (QueryNOK, uu____8328)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Exn.raise uu___1056_8315)))
let run_compute :
  'Auu____8344 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
            'Auu____8344) FStar_Util.either)
  =
  fun st ->
    fun term ->
      fun rules ->
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules1 -> rules1
             | FStar_Pervasives_Native.None ->
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.Iota;
                 FStar_TypeChecker_Env.Zeta;
                 FStar_TypeChecker_Env.UnfoldUntil
                   FStar_Syntax_Syntax.delta_constant])
            [FStar_TypeChecker_Env.Inlining;
            FStar_TypeChecker_Env.Eager_unfolding;
            FStar_TypeChecker_Env.UnfoldTac;
            FStar_TypeChecker_Env.Primops] in
        let normalize_term1 tcenv rules2 t =
          FStar_TypeChecker_Normalize.normalize rules2 tcenv t in
        run_with_parsed_and_tc_term st term (Prims.parse_int "0")
          (Prims.parse_int "0")
          (fun tcenv ->
             fun def ->
               let normalized = normalize_term1 tcenv rules1 def in
               let uu____8422 =
                 let uu____8423 =
                   FStar_QueryHelper.term_to_string tcenv normalized in
                 FStar_Util.JsonStr uu____8423 in
               (QueryOK, uu____8422))
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NameContainsStr _0 -> true | uu____8458 -> false
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee -> match projectee with | NameContainsStr _0 -> _0
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeContainsLid _0 -> true | uu____8480 -> false
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TypeContainsLid _0 -> _0
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | { st_negate; st_term;_} -> st_negate
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee -> match projectee with | { st_negate; st_term;_} -> st_term
let (st_cost : search_term' -> Prims.int) =
  fun uu___8_8515 ->
    match uu___8_8515 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> (Prims.parse_int "1")
type search_candidate =
  {
  sc_lid: FStar_Ident.lid ;
  sc_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref ;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
    }
let (__proj__Mksearch_candidate__item__sc_lid :
  search_candidate -> FStar_Ident.lid) =
  fun projectee ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_lid
let (__proj__Mksearch_candidate__item__sc_typ :
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref)
  =
  fun projectee ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_typ
let (__proj__Mksearch_candidate__item__sc_fvars :
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref)
  =
  fun projectee ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_fvars
let (sc_of_lid : FStar_Ident.lid -> search_candidate) =
  fun lid ->
    let uu____8649 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____8656 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____8649; sc_fvars = uu____8656 }
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv ->
    fun sc ->
      let uu____8680 = FStar_ST.op_Bang sc.sc_typ in
      match uu____8680 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let typ =
            let uu____8708 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____8708 with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____8727, typ), uu____8729) ->
                typ in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
let (sc_fvars :
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lident FStar_Util.set)
  =
  fun tcenv ->
    fun sc ->
      let uu____8779 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____8779 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None ->
          let fv =
            let uu____8823 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____8823 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv ->
    fun sc ->
      let typ_str =
        let uu____8867 = sc_typ tcenv sc in
        FStar_QueryHelper.term_to_string tcenv uu____8867 in
      let uu____8868 =
        let uu____8876 =
          let uu____8882 =
            let uu____8883 =
              let uu____8885 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              uu____8885.FStar_Ident.str in
            FStar_Util.JsonStr uu____8883 in
          ("lid", uu____8882) in
        [uu____8876; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____8868
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidSearch uu____8918 -> true
    | uu____8921 -> false
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidSearch uu____8931 -> uu____8931
let run_search :
  'Auu____8940 .
    FStar_JsonHelper.repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
          'Auu____8940) FStar_Util.either)
  =
  fun st ->
    fun search_str ->
      let tcenv = st.FStar_JsonHelper.repl_env in
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____8987 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____8987 in
        found <> term.st_negate in
      let parse1 search_str1 =
        let parse_one term =
          let negate = FStar_Util.starts_with term "-" in
          let term1 =
            if negate
            then FStar_Util.substring_from term (Prims.parse_int "1")
            else term in
          let beg_quote = FStar_Util.starts_with term1 "\"" in
          let end_quote = FStar_Util.ends_with term1 "\"" in
          let strip_quotes str =
            if (FStar_String.length str) < (Prims.parse_int "2")
            then FStar_Exn.raise (InvalidSearch "Empty search term")
            else
              FStar_Util.substring str (Prims.parse_int "1")
                ((FStar_String.length term1) - (Prims.parse_int "2")) in
          let parsed =
            if beg_quote <> end_quote
            then
              let uu____9046 =
                let uu____9047 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____9047 in
              FStar_Exn.raise uu____9046
            else
              if beg_quote
              then
                (let uu____9053 = strip_quotes term1 in
                 NameContainsStr uu____9053)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____9058 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____9058 with
                 | FStar_Pervasives_Native.None ->
                     let uu____9061 =
                       let uu____9062 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____9062 in
                     FStar_Exn.raise uu____9061
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____9090 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____9090 in
      let results =
        try
          (fun uu___1170_9124 ->
             match () with
             | () ->
                 let terms = parse1 search_str in
                 let all_lidents = FStar_TypeChecker_Env.lidents tcenv in
                 let all_candidates = FStar_List.map sc_of_lid all_lidents in
                 let matches_all candidate =
                   FStar_List.for_all (st_matches candidate) terms in
                 let cmp r1 r2 =
                   FStar_Util.compare (r1.sc_lid).FStar_Ident.str
                     (r2.sc_lid).FStar_Ident.str in
                 let results = FStar_List.filter matches_all all_candidates in
                 let sorted1 = FStar_Util.sort_with cmp results in
                 let js =
                   FStar_List.map (json_of_search_result tcenv) sorted1 in
                 (match results with
                  | [] ->
                      let kwds =
                        let uu____9172 = FStar_List.map pprint_one terms in
                        FStar_Util.concat_l " " uu____9172 in
                      let uu____9178 =
                        let uu____9179 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds in
                        InvalidSearch uu____9179 in
                      FStar_Exn.raise uu____9178
                  | uu____9186 -> (QueryOK, (FStar_Util.JsonList js)))) ()
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
      (results, (FStar_Util.Inl st))
let (run_query :
  FStar_JsonHelper.repl_state ->
    query' ->
      ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
        Prims.int) FStar_Util.either))
  =
  fun st ->
    fun q ->
      match q with
      | Exit -> run_exit st
      | DescribeProtocol -> run_describe_protocol st
      | DescribeRepl -> run_describe_repl st
      | GenericError message -> run_generic_error st message
      | ProtocolViolation query -> run_protocol_violation st query
      | Segment c -> run_segment st c
      | VfsAdd (fname, contents) -> run_vfs_add st fname contents
      | Push pquery -> run_push st pquery
      | Pop -> run_pop st
      | AutoComplete (search_term, context) ->
          run_autocomplete st search_term context
      | Lookup (symbol, context, pos_opt, rq_info) ->
          run_lookup st symbol context pos_opt rq_info
      | Compute (term, rules) -> run_compute st term rules
      | Search term -> run_search st term
let (validate_query : FStar_JsonHelper.repl_state -> query -> query) =
  fun st ->
    fun q ->
      match q.qq with
      | Push
          { push_kind = SyntaxCheck; push_code = uu____9317;
            push_line = uu____9318; push_column = uu____9319;
            push_peek_only = false;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____9325 ->
          (match st.FStar_JsonHelper.repl_curmod with
           | FStar_Pervasives_Native.None when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____9327 -> q)
let (validate_and_run_query :
  FStar_JsonHelper.repl_state ->
    query ->
      ((query_status * FStar_Util.json) * (FStar_JsonHelper.repl_state,
        Prims.int) FStar_Util.either))
  =
  fun st ->
    fun query ->
      let query1 = validate_query st query in
      FStar_ST.op_Colon_Equals repl_current_qid
        (FStar_Pervasives_Native.Some (query1.qid));
      run_query st query1.qq
let (js_repl_eval :
  FStar_JsonHelper.repl_state ->
    query ->
      (FStar_Util.json * (FStar_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query ->
      let uu____9400 = validate_and_run_query st query in
      match uu____9400 with
      | ((status, response), st_opt) ->
          let js_response = json_of_response query.qid status response in
          (js_response, st_opt)
let (js_repl_eval_js :
  FStar_JsonHelper.repl_state ->
    FStar_Util.json ->
      (FStar_Util.json * (FStar_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query_js ->
      let uu____9466 = deserialize_interactive_query query_js in
      js_repl_eval st uu____9466
let (js_repl_eval_str :
  FStar_JsonHelper.repl_state ->
    Prims.string ->
      (Prims.string * (FStar_JsonHelper.repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query_str ->
      let uu____9490 =
        let uu____9500 = parse_interactive_query query_str in
        js_repl_eval st uu____9500 in
      match uu____9490 with
      | (js_response, st_opt) ->
          let uu____9523 = FStar_Util.string_of_json js_response in
          (uu____9523, st_opt)
let (js_repl_init_opts : unit -> unit) =
  fun uu____9536 ->
    let uu____9537 = FStar_Options.parse_cmd_line () in
    match uu____9537 with
    | (res, fnames) ->
        (match res with
         | FStar_Getopt.Error msg ->
             failwith (Prims.op_Hat "repl_init: " msg)
         | FStar_Getopt.Help -> failwith "repl_init: --help unexpected"
         | FStar_Getopt.Success ->
             (match fnames with
              | [] ->
                  failwith
                    "repl_init: No file name given in --ide invocation"
              | h::uu____9560::uu____9561 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____9570 -> ()))
let rec (go : FStar_JsonHelper.repl_state -> Prims.int) =
  fun st ->
    let query = read_interactive_query st.FStar_JsonHelper.repl_stdin in
    let uu____9583 = validate_and_run_query st query in
    match uu____9583 with
    | ((status, response), state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____9636 =
      let uu____9639 = FStar_ST.op_Bang issues in e :: uu____9639 in
    FStar_ST.op_Colon_Equals issues uu____9636 in
  let count_errors uu____9693 =
    let uu____9694 =
      let uu____9697 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____9697 in
    FStar_List.length uu____9694 in
  let report uu____9732 =
    let uu____9733 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____9733 in
  let clear1 uu____9764 = FStar_ST.op_Colon_Equals issues [] in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report;
    FStar_Errors.eh_clear = clear1
  }
let (interactive_printer : (FStar_Util.json -> unit) -> FStar_Util.printer) =
  fun printer ->
    {
      FStar_Util.printer_prinfo =
        (fun s -> forward_message printer "info" (FStar_Util.JsonStr s));
      FStar_Util.printer_prwarning =
        (fun s -> forward_message printer "warning" (FStar_Util.JsonStr s));
      FStar_Util.printer_prerror =
        (fun s -> forward_message printer "error" (FStar_Util.JsonStr s));
      FStar_Util.printer_prgeneric =
        (fun label ->
           fun get_string ->
             fun get_json ->
               let uu____9825 = get_json () in
               forward_message printer label uu____9825)
    }
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
let (initial_range : FStar_Range.range) =
  let uu____9839 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  let uu____9842 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  FStar_Range.mk_range "<input>" uu____9839 uu____9842
let (build_initial_repl_state : Prims.string -> FStar_JsonHelper.repl_state)
  =
  fun filename ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range in
    let uu____9856 = FStar_Util.open_stdin () in
    {
      FStar_JsonHelper.repl_line = (Prims.parse_int "1");
      FStar_JsonHelper.repl_column = (Prims.parse_int "0");
      FStar_JsonHelper.repl_fname = filename;
      FStar_JsonHelper.repl_deps_stack = [];
      FStar_JsonHelper.repl_curmod = FStar_Pervasives_Native.None;
      FStar_JsonHelper.repl_env = env1;
      FStar_JsonHelper.repl_stdin = uu____9856;
      FStar_JsonHelper.repl_names = FStar_Interactive_CompletionTable.empty
    }
let interactive_mode' :
  'Auu____9872 . FStar_JsonHelper.repl_state -> 'Auu____9872 =
  fun init_st ->
    write_hello ();
    (let exit_code =
       let uu____9881 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____9881
       then
         let uu____9885 =
           let uu____9887 = FStar_Options.file_list () in
           FStar_List.hd uu____9887 in
         FStar_SMTEncoding_Solver.with_hints_db uu____9885
           (fun uu____9894 -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    install_ide_mode_hooks FStar_JsonHelper.write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____9908 =
       let uu____9910 = FStar_Options.codegen () in
       FStar_Option.isSome uu____9910 in
     if uu____9908
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename in
     let uu____9919 = FStar_Options.trace_error () in
     if uu____9919
     then interactive_mode' init1
     else
       (try
          (fun uu___1318_9925 ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___1317_9928 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1317_9928)))