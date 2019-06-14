open Prims
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string -> (repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun msg ->
      let uu____60 = FStar_TypeChecker_Tc.snapshot_context env msg in
      match uu____60 with
      | (ctx_depth, env1) ->
          let uu____104 = FStar_Options.snapshot () in
          (match uu____104 with
           | (opt_depth, ()) -> ((ctx_depth, opt_depth), env1))
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver1 ->
    fun msg ->
      fun uu____150 ->
        match uu____150 with
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
    match projectee with | SyntaxCheck -> true | uu____217 -> false
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | LaxCheck -> true | uu____228 -> false
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | FullCheck -> true | uu____239 -> false
let (set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun check_kind ->
      let uu___32_252 = env in
      let uu____253 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___32_252.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___32_252.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___32_252.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___32_252.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___32_252.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___32_252.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___32_252.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___32_252.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___32_252.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___32_252.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___32_252.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___32_252.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___32_252.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___32_252.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___32_252.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___32_252.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___32_252.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___32_252.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___32_252.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___32_252.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___32_252.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___32_252.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___32_252.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___32_252.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___32_252.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___32_252.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___32_252.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___32_252.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___32_252.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___32_252.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___32_252.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___32_252.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___32_252.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___32_252.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___32_252.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___32_252.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___32_252.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___32_252.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___32_252.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___32_252.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____253;
        FStar_TypeChecker_Env.nbe = (uu___32_252.FStar_TypeChecker_Env.nbe)
      }
let with_captured_errors' :
  'Auu____263 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____263 FStar_Pervasives_Native.option)
          -> 'Auu____263 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        try
          (fun uu___38_293 ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____299 -> f env)) ()
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
            ((let uu____317 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.log_issue uu____317
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e, msg, r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e, msg) ->
            ((let uu____347 =
                let uu____357 =
                  let uu____365 = FStar_TypeChecker_Env.get_range env in
                  (e, msg, uu____365) in
                [uu____357] in
              FStar_TypeChecker_Err.add_errors env uu____347);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop -> FStar_Pervasives_Native.None
let with_captured_errors :
  'Auu____390 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____390 FStar_Pervasives_Native.option)
          -> 'Auu____390 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        let uu____417 = FStar_Options.trace_error () in
        if uu____417
        then f env
        else with_captured_errors' env sigint_handler f
type timed_fname = {
  tf_fname: Prims.string ;
  tf_modtime: FStar_Util.time }
let (__proj__Mktimed_fname__item__tf_fname : timed_fname -> Prims.string) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_fname
let (__proj__Mktimed_fname__item__tf_modtime :
  timed_fname -> FStar_Util.time) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_modtime
let (t0 : FStar_Util.time) = FStar_Util.now ()
let (tf_of_fname : Prims.string -> timed_fname) =
  fun fname ->
    let uu____464 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname in
    { tf_fname = fname; tf_modtime = uu____464 }
let (dummy_tf_of_fname : Prims.string -> timed_fname) =
  fun fname -> { tf_fname = fname; tf_modtime = t0 }
let (string_of_timed_fname : timed_fname -> Prims.string) =
  fun uu____479 ->
    match uu____479 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____489 = FStar_Util.string_of_time modtime in
           FStar_Util.format2 "{ %s; %s }" fname uu____489)
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
type optmod_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type repl_task =
  | LDInterleaved of (timed_fname * timed_fname) 
  | LDSingle of timed_fname 
  | LDInterfaceOfCurrentFile of timed_fname 
  | PushFragment of FStar_Parser_ParseIt.input_frag 
  | Noop 
let (uu___is_LDInterleaved : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDInterleaved _0 -> true | uu____644 -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu____675 -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____694 -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu____713 -> false
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu____731 -> false
type env_t = FStar_TypeChecker_Env.env
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_fname: Prims.string ;
  repl_deps_stack: (repl_depth_t * (repl_task * repl_state)) Prims.list ;
  repl_curmod: optmod_t ;
  repl_env: env_t ;
  repl_stdin: FStar_Util.stream_reader ;
  repl_names: FStar_Interactive_CompletionTable.table }
let (__proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_line
let (__proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_column
let (__proj__Mkrepl_state__item__repl_fname : repl_state -> Prims.string) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_fname
let (__proj__Mkrepl_state__item__repl_deps_stack :
  repl_state -> (repl_depth_t * (repl_task * repl_state)) Prims.list) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_deps_stack
let (__proj__Mkrepl_state__item__repl_curmod : repl_state -> optmod_t) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_curmod
let (__proj__Mkrepl_state__item__repl_env : repl_state -> env_t) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_env
let (__proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Util.stream_reader) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_stdin
let (__proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_names
type repl_stack_entry_t = (repl_depth_t * (repl_task * repl_state))
type repl_stack_t = (repl_depth_t * (repl_task * repl_state)) Prims.list
let (repl_current_qid :
  Prims.string FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (repl_stack : repl_stack_t FStar_ST.ref) = FStar_Util.mk_ref []
let (pop_repl : Prims.string -> repl_state -> repl_state) =
  fun msg ->
    fun st ->
      let uu____1080 = FStar_ST.op_Bang repl_stack in
      match uu____1080 with
      | [] -> failwith "Too many pops"
      | (depth, (uu____1110, st'))::stack_tl ->
          let env =
            rollback_env (st.repl_env).FStar_TypeChecker_Env.solver msg depth in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____1157 = FStar_Util.physical_equality env st'.repl_env in
            FStar_Common.runtime_assert uu____1157 "Inconsistent stack state");
           st')
let (push_repl :
  Prims.string -> push_kind -> repl_task -> repl_state -> repl_state) =
  fun msg ->
    fun push_kind ->
      fun task ->
        fun st ->
          let uu____1183 = snapshot_env st.repl_env msg in
          match uu____1183 with
          | (depth, env) ->
              ((let uu____1191 =
                  let uu____1192 = FStar_ST.op_Bang repl_stack in
                  (depth, (task, st)) :: uu____1192 in
                FStar_ST.op_Colon_Equals repl_stack uu____1191);
               (let uu___141_1253 = st in
                let uu____1254 = set_check_kind env push_kind in
                {
                  repl_line = (uu___141_1253.repl_line);
                  repl_column = (uu___141_1253.repl_column);
                  repl_fname = (uu___141_1253.repl_fname);
                  repl_deps_stack = (uu___141_1253.repl_deps_stack);
                  repl_curmod = (uu___141_1253.repl_curmod);
                  repl_env = uu____1254;
                  repl_stdin = (uu___141_1253.repl_stdin);
                  repl_names = (uu___141_1253.repl_names)
                }))
let (nothing_left_to_pop : repl_state -> Prims.bool) =
  fun st ->
    let uu____1262 =
      let uu____1263 = FStar_ST.op_Bang repl_stack in
      FStar_List.length uu____1263 in
    uu____1262 = (FStar_List.length st.repl_deps_stack)
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of (FStar_Syntax_Syntax.binding,
  FStar_TypeChecker_Env.sig_binding) FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTAlias _0 -> true | uu____1363 -> false
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee -> match projectee with | NTAlias _0 -> _0
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTOpen _0 -> true | uu____1404 -> false
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee -> match projectee with | NTOpen _0 -> _0
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTInclude _0 -> true | uu____1439 -> false
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee -> match projectee with | NTInclude _0 -> _0
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTBinding _0 -> true | uu____1474 -> false
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
              let uu____1542 = FStar_Ident.text_of_id id1 in
              let uu____1544 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                uu____1542 [] uu____1544
            else table
        | NTOpen (host, (included, kind)) ->
            if is_cur_mod host
            then
              let uu____1552 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____1552
            else table
        | NTInclude (host, included) ->
            let uu____1558 =
              if is_cur_mod host then [] else query_of_lid host in
            let uu____1563 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____1558 uu____1563
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid, uu____1575)) -> [lid]
              | FStar_Util.Inr (lids, uu____1593) -> lids
              | uu____1598 -> [] in
            FStar_List.fold_left
              (fun tbl ->
                 fun lid ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns in
                   let uu____1615 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____1615 lid) table lids
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
              let uu____1646 = FStar_Syntax_Syntax.mod_name md in
              uu____1646.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let (commit_name_tracking :
  repl_state -> name_tracking_event Prims.list -> repl_state) =
  fun st ->
    fun name_events ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events in
      let uu___201_1672 = st in
      {
        repl_line = (uu___201_1672.repl_line);
        repl_column = (uu___201_1672.repl_column);
        repl_fname = (uu___201_1672.repl_fname);
        repl_deps_stack = (uu___201_1672.repl_deps_stack);
        repl_curmod = (uu___201_1672.repl_curmod);
        repl_env = (uu___201_1672.repl_env);
        repl_stdin = (uu___201_1672.repl_stdin);
        repl_names = names1
      }
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____1688 ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____1702 =
        let uu____1705 = FStar_ST.op_Bang events in evt :: uu____1705 in
      FStar_ST.op_Colon_Equals events uu____1702 in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1 ->
             fun op ->
               let uu____1766 =
                 let uu____1767 =
                   let uu____1772 = FStar_Syntax_DsEnv.current_module dsenv1 in
                   (uu____1772, op) in
                 NTOpen uu____1767 in
               push_event uu____1766);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1 ->
             fun ns ->
               let uu____1778 =
                 let uu____1779 =
                   let uu____1784 = FStar_Syntax_DsEnv.current_module dsenv1 in
                   (uu____1784, ns) in
                 NTInclude uu____1779 in
               push_event uu____1778);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1 ->
             fun x ->
               fun l ->
                 let uu____1792 =
                   let uu____1793 =
                     let uu____1800 =
                       FStar_Syntax_DsEnv.current_module dsenv1 in
                     (uu____1800, x, l) in
                   NTAlias uu____1793 in
                 push_event uu____1792)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1805 -> fun s -> push_event (NTBinding s))
      })
let (track_name_changes :
  env_t -> (env_t * (env_t -> (env_t * name_tracking_event Prims.list)))) =
  fun env ->
    let set_hooks dshooks tchooks env1 =
      let uu____1859 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv1 ->
             let uu____1867 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks in
             ((), uu____1867)) in
      match uu____1859 with
      | ((), tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu____1869 =
      let uu____1874 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu____1875 = FStar_TypeChecker_Env.tc_hooks env in
      (uu____1874, uu____1875) in
    match uu____1869 with
    | (old_dshooks, old_tchooks) ->
        let uu____1891 = fresh_name_tracking_hooks () in
        (match uu____1891 with
         | (events, new_dshooks, new_tchooks) ->
             let uu____1926 = set_hooks new_dshooks new_tchooks env in
             (uu____1926,
               ((fun env1 ->
                   let uu____1940 = set_hooks old_dshooks old_tchooks env1 in
                   let uu____1941 =
                     let uu____1944 = FStar_ST.op_Bang events in
                     FStar_List.rev uu____1944 in
                   (uu____1940, uu____1941)))))
let (string_of_repl_task : repl_task -> Prims.string) =
  fun uu___0_1978 ->
    match uu___0_1978 with
    | LDInterleaved (intf, impl) ->
        let uu____1982 = string_of_timed_fname intf in
        let uu____1984 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1982 uu____1984
    | LDSingle intf_or_impl ->
        let uu____1988 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____1988
    | LDInterfaceOfCurrentFile intf ->
        let uu____1992 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1992
    | PushFragment frag ->
        FStar_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
    | Noop -> "Noop {}"
let (tc_one :
  env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> FStar_TypeChecker_Env.env_t)
  =
  fun env ->
    fun intf_opt ->
      fun modf ->
        let uu____2022 =
          let uu____2027 =
            let uu____2028 =
              let uu____2034 = FStar_TypeChecker_Env.dep_graph env in
              FStar_Parser_Dep.parsing_data_of uu____2034 in
            FStar_All.pipe_right modf uu____2028 in
          FStar_Universal.tc_one_file_for_ide env intf_opt modf uu____2027 in
        match uu____2022 with | (uu____2036, env1) -> env1
let (run_repl_task : optmod_t -> env_t -> repl_task -> (optmod_t * env_t)) =
  fun curmod ->
    fun env ->
      fun task ->
        match task with
        | LDInterleaved (intf, impl) ->
            let uu____2064 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname in
            (curmod, uu____2064)
        | LDSingle intf_or_impl ->
            let uu____2067 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname in
            (curmod, uu____2067)
        | LDInterfaceOfCurrentFile intf ->
            let uu____2070 =
              FStar_Universal.load_interface_decls env intf.tf_fname in
            (curmod, uu____2070)
        | PushFragment frag ->
            FStar_Universal.tc_one_fragment curmod env frag
        | Noop -> (curmod, env)
let (repl_ld_tasks_of_deps :
  Prims.string Prims.list -> repl_task Prims.list -> repl_task Prims.list) =
  fun deps ->
    fun final_tasks ->
      let wrap = dummy_tf_of_fname in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____2136 = aux deps' final_tasks1 in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____2136
        | intf_or_impl::deps' ->
            let uu____2146 = aux deps' final_tasks1 in
            (LDSingle (wrap intf_or_impl)) :: uu____2146
        | [] -> final_tasks1 in
      aux deps final_tasks
let (deps_and_repl_ld_tasks_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * repl_task Prims.list * FStar_Parser_Dep.deps))
  =
  fun filename ->
    let get_mod_name fname = FStar_Parser_Dep.lowercase_module_name fname in
    let our_mod_name = get_mod_name filename in
    let has_our_mod_name f =
      let uu____2200 = get_mod_name f in uu____2200 = our_mod_name in
    let uu____2203 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_CheckedFiles.load_parsing_data_from_cache in
    match uu____2203 with
    | (deps, dep_graph1) ->
        let uu____2232 = FStar_List.partition has_our_mod_name deps in
        (match uu____2232 with
         | (same_name, real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____2282 =
                       let uu____2284 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu____2284 in
                     if uu____2282
                     then
                       let uu____2287 =
                         let uu____2293 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.Fatal_MissingInterface, uu____2293) in
                       FStar_Errors.raise_err uu____2287
                     else ());
                    (let uu____2300 =
                       let uu____2302 =
                         FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu____2302 in
                     if uu____2300
                     then
                       let uu____2305 =
                         let uu____2311 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____2311) in
                       FStar_Errors.raise_err uu____2305
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____2321 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu____2332 =
                       let uu____2338 =
                         FStar_Util.format message [our_mod_name; mods_str] in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____2338) in
                     FStar_Errors.raise_err uu____2332);
                    []) in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
             (real_deps, tasks, dep_graph1))
let (update_task_timestamps : repl_task -> repl_task) =
  fun uu___1_2357 ->
    match uu___1_2357 with
    | LDInterleaved (intf, impl) ->
        let uu____2360 =
          let uu____2365 = tf_of_fname intf.tf_fname in
          let uu____2366 = tf_of_fname impl.tf_fname in
          (uu____2365, uu____2366) in
        LDInterleaved uu____2360
    | LDSingle intf_or_impl ->
        let uu____2368 = tf_of_fname intf_or_impl.tf_fname in
        LDSingle uu____2368
    | LDInterfaceOfCurrentFile intf ->
        let uu____2370 = tf_of_fname intf.tf_fname in
        LDInterfaceOfCurrentFile uu____2370
    | other -> other
let (run_repl_transaction :
  repl_state ->
    push_kind -> Prims.bool -> repl_task -> (Prims.bool * repl_state))
  =
  fun st ->
    fun push_kind ->
      fun must_rollback ->
        fun task ->
          let st1 = push_repl "run_repl_transaction" push_kind task st in
          let uu____2402 = track_name_changes st1.repl_env in
          match uu____2402 with
          | (env, finish_name_tracking) ->
              let check_success uu____2447 =
                (let uu____2450 = FStar_Errors.get_err_count () in
                 uu____2450 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback) in
              let uu____2454 =
                let uu____2462 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1 ->
                       let uu____2476 =
                         run_repl_task st1.repl_curmod env1 task in
                       FStar_All.pipe_left
                         (fun _2495 -> FStar_Pervasives_Native.Some _2495)
                         uu____2476) in
                match uu____2462 with
                | FStar_Pervasives_Native.Some (curmod, env1) when
                    check_success () -> (curmod, env1, true)
                | uu____2511 -> ((st1.repl_curmod), env, false) in
              (match uu____2454 with
               | (curmod, env1, success) ->
                   let uu____2530 = finish_name_tracking env1 in
                   (match uu____2530 with
                    | (env2, name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___341_2551 = st1 in
                              {
                                repl_line = (uu___341_2551.repl_line);
                                repl_column = (uu___341_2551.repl_column);
                                repl_fname = (uu___341_2551.repl_fname);
                                repl_deps_stack =
                                  (uu___341_2551.repl_deps_stack);
                                repl_curmod = curmod;
                                repl_env = env2;
                                repl_stdin = (uu___341_2551.repl_stdin);
                                repl_names = (uu___341_2551.repl_names)
                              } in
                            commit_name_tracking st2 name_events
                          else pop_repl "run_repl_transaction" st1 in
                        (success, st2)))
let (run_repl_ld_transactions :
  repl_state ->
    repl_task Prims.list ->
      (repl_task -> unit) -> (repl_state, repl_state) FStar_Util.either)
  =
  fun st ->
    fun tasks ->
      fun progress_callback ->
        let debug1 verb task =
          let uu____2598 = FStar_Options.debug_any () in
          if uu____2598
          then
            let uu____2601 = string_of_repl_task task in
            FStar_Util.print2 "%s %s" verb uu____2601
          else () in
        let rec revert_many st1 uu___2_2626 =
          match uu___2_2626 with
          | [] -> st1
          | (_id, (task, _st'))::entries ->
              (debug1 "Reverting" task;
               (let st' = pop_repl "run_repl_ls_transactions" st1 in
                let dep_graph1 = FStar_TypeChecker_Env.dep_graph st1.repl_env in
                let st'1 =
                  let uu___367_2679 = st' in
                  let uu____2680 =
                    FStar_TypeChecker_Env.set_dep_graph st'.repl_env
                      dep_graph1 in
                  {
                    repl_line = (uu___367_2679.repl_line);
                    repl_column = (uu___367_2679.repl_column);
                    repl_fname = (uu___367_2679.repl_fname);
                    repl_deps_stack = (uu___367_2679.repl_deps_stack);
                    repl_curmod = (uu___367_2679.repl_curmod);
                    repl_env = uu____2680;
                    repl_stdin = (uu___367_2679.repl_stdin);
                    repl_names = (uu___367_2679.repl_names)
                  } in
                revert_many st'1 entries)) in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([], []) -> FStar_Util.Inl st1
          | (task::tasks2, []) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____2733 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu____2733 (fun a1 -> ()));
               (let timestamped_task = update_task_timestamps task in
                let push_kind =
                  let uu____2737 = FStar_Options.lax () in
                  if uu____2737 then LaxCheck else FullCheck in
                let uu____2742 =
                  run_repl_transaction st1 push_kind false timestamped_task in
                match uu____2742 with
                | (success, st2) ->
                    if success
                    then
                      let uu____2762 =
                        let uu___392_2763 = st2 in
                        let uu____2764 = FStar_ST.op_Bang repl_stack in
                        {
                          repl_line = (uu___392_2763.repl_line);
                          repl_column = (uu___392_2763.repl_column);
                          repl_fname = (uu___392_2763.repl_fname);
                          repl_deps_stack = uu____2764;
                          repl_curmod = (uu___392_2763.repl_curmod);
                          repl_env = (uu___392_2763.repl_env);
                          repl_stdin = (uu___392_2763.repl_stdin);
                          repl_names = (uu___392_2763.repl_names)
                        } in
                      aux uu____2762 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2, prev::previous1) when
              let uu____2808 = update_task_timestamps task in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____2808
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2, previous1) ->
              let uu____2825 = revert_many st1 previous1 in
              aux uu____2825 tasks2 [] in
        aux st tasks (FStar_List.rev st.repl_deps_stack)
let (json_debug : FStar_Util.json -> Prims.string) =
  fun uu___3_2840 ->
    match uu___3_2840 with
    | FStar_Util.JsonNull -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2854 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2854
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2860 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2864 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnexpectedJsonType uu____2890 -> true
    | uu____2897 -> false
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee ->
    match projectee with | UnexpectedJsonType uu____2915 -> uu____2915
let js_fail : 'Auu____2928 . Prims.string -> FStar_Util.json -> 'Auu____2928
  =
  fun expected ->
    fun got -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___4_2948 ->
    match uu___4_2948 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___5_2961 ->
    match uu___5_2961 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list :
  'Auu____2975 .
    (FStar_Util.json -> 'Auu____2975) ->
      FStar_Util.json -> 'Auu____2975 Prims.list
  =
  fun k ->
    fun uu___6_2990 ->
      match uu___6_2990 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___7_3012 ->
    match uu___7_3012 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let (js_pushkind : FStar_Util.json -> push_kind) =
  fun s ->
    let uu____3043 = js_str s in
    match uu____3043 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____3048 -> js_fail "push_kind" s
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s ->
    let uu____3057 = js_str s in
    match uu____3057 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____3065 -> js_fail "reduction rule" s
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKCode -> true | uu____3094 -> false
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKOption _0 -> true | uu____3107 -> false
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKOption _0 -> _0
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____3135 -> false
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee -> match projectee with | CKModuleOrNamespace _0 -> _0
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____3173 = js_str k1 in
        (match uu____3173 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____3201 ->
             js_fail
               "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
type lookup_context =
  | LKSymbolOnly 
  | LKModule 
  | LKOption 
  | LKCode 
let (uu___is_LKSymbolOnly : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKSymbolOnly -> true | uu____3213 -> false
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKModule -> true | uu____3224 -> false
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKOption -> true | uu____3235 -> false
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKCode -> true | uu____3246 -> false
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____3259 = js_str k1 in
        (match uu____3259 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____3269 ->
             js_fail
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
  fun projectee -> match projectee with | Exit -> true | uu____3386 -> false
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeProtocol -> true | uu____3397 -> false
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeRepl -> true | uu____3408 -> false
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Segment _0 -> true | uu____3421 -> false
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Segment _0 -> _0
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu____3442 -> false
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Push _0 -> true | uu____3454 -> false
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | VfsAdd _0 -> true | uu____3481 -> false
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee -> match projectee with | VfsAdd _0 -> _0
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | AutoComplete _0 -> true | uu____3529 -> false
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee -> match projectee with | AutoComplete _0 -> _0
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Lookup _0 -> true | uu____3577 -> false
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee -> match projectee with | Lookup _0 -> _0
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Compute _0 -> true | uu____3647 -> false
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Compute _0 -> _0
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Search _0 -> true | uu____3694 -> false
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Search _0 -> _0
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | GenericError _0 -> true | uu____3717 -> false
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | GenericError _0 -> _0
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | ProtocolViolation _0 -> true | uu____3740 -> false
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | ProtocolViolation _0 -> _0
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___8_3778 ->
    match uu___8_3778 with
    | Exit -> false
    | DescribeProtocol -> false
    | DescribeRepl -> false
    | Segment uu____3783 -> false
    | Pop -> false
    | Push
        { push_kind = uu____3787; push_code = uu____3788;
          push_line = uu____3789; push_column = uu____3790;
          push_peek_only = false;_}
        -> false
    | VfsAdd uu____3796 -> false
    | GenericError uu____3806 -> false
    | ProtocolViolation uu____3809 -> false
    | Push uu____3812 -> true
    | AutoComplete uu____3814 -> true
    | Lookup uu____3821 -> true
    | Compute uu____3837 -> true
    | Search uu____3848 -> true
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
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidQuery uu____3914 -> true
    | uu____3917 -> false
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidQuery uu____3927 -> uu____3927
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let (uu___is_QueryOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryOK -> true | uu____3938 -> false
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryNOK -> true | uu____3949 -> false
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with
    | QueryViolatesProtocol -> true
    | uu____3960 -> false
let try_assoc :
  'Auu____3971 'Auu____3972 .
    'Auu____3971 ->
      ('Auu____3971 * 'Auu____3972) Prims.list ->
        'Auu____3972 FStar_Pervasives_Native.option
  =
  fun key ->
    fun a ->
      let uu____3997 =
        FStar_Util.try_find
          (fun uu____4011 ->
             match uu____4011 with | (k, uu____4018) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____3997
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____4043 =
          let uu____4044 =
            let uu____4046 = json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____4046 in
          ProtocolViolation uu____4044 in
        { qq = uu____4043; qid }
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json ->
    let assoc1 errloc key a =
      let uu____4089 = try_assoc key a in
      match uu____4089 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____4094 =
            let uu____4095 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____4095 in
          FStar_Exn.raise uu____4094 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____4115 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____4115 js_str in
    try
      (fun uu___544_4125 ->
         match () with
         | () ->
             let query =
               let uu____4128 = assoc1 "query" "query" request in
               FStar_All.pipe_right uu____4128 js_str in
             let args =
               let uu____4140 = assoc1 "query" "args" request in
               FStar_All.pipe_right uu____4140 js_assoc in
             let arg k = assoc1 "[args]" k args in
             let try_arg k =
               let uu____4169 = try_assoc k args in
               match uu____4169 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull) ->
                   FStar_Pervasives_Native.None
               | other -> other in
             let uu____4178 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____4184 =
                     let uu____4186 = arg "code" in
                     FStar_All.pipe_right uu____4186 js_str in
                   Segment uu____4184
               | "peek" ->
                   let uu____4190 =
                     let uu____4191 =
                       let uu____4192 = arg "kind" in
                       FStar_All.pipe_right uu____4192 js_pushkind in
                     let uu____4194 =
                       let uu____4196 = arg "code" in
                       FStar_All.pipe_right uu____4196 js_str in
                     let uu____4199 =
                       let uu____4201 = arg "line" in
                       FStar_All.pipe_right uu____4201 js_int in
                     let uu____4204 =
                       let uu____4206 = arg "column" in
                       FStar_All.pipe_right uu____4206 js_int in
                     {
                       push_kind = uu____4191;
                       push_code = uu____4194;
                       push_line = uu____4199;
                       push_column = uu____4204;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____4190
               | "push" ->
                   let uu____4212 =
                     let uu____4213 =
                       let uu____4214 = arg "kind" in
                       FStar_All.pipe_right uu____4214 js_pushkind in
                     let uu____4216 =
                       let uu____4218 = arg "code" in
                       FStar_All.pipe_right uu____4218 js_str in
                     let uu____4221 =
                       let uu____4223 = arg "line" in
                       FStar_All.pipe_right uu____4223 js_int in
                     let uu____4226 =
                       let uu____4228 = arg "column" in
                       FStar_All.pipe_right uu____4228 js_int in
                     {
                       push_kind = uu____4213;
                       push_code = uu____4216;
                       push_line = uu____4221;
                       push_column = uu____4226;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____4212
               | "autocomplete" ->
                   let uu____4234 =
                     let uu____4240 =
                       let uu____4242 = arg "partial-symbol" in
                       FStar_All.pipe_right uu____4242 js_str in
                     let uu____4245 =
                       let uu____4246 = try_arg "context" in
                       FStar_All.pipe_right uu____4246
                         js_optional_completion_context in
                     (uu____4240, uu____4245) in
                   AutoComplete uu____4234
               | "lookup" ->
                   let uu____4254 =
                     let uu____4269 =
                       let uu____4271 = arg "symbol" in
                       FStar_All.pipe_right uu____4271 js_str in
                     let uu____4274 =
                       let uu____4275 = try_arg "context" in
                       FStar_All.pipe_right uu____4275
                         js_optional_lookup_context in
                     let uu____4281 =
                       let uu____4284 =
                         let uu____4294 = try_arg "location" in
                         FStar_All.pipe_right uu____4294
                           (FStar_Util.map_option js_assoc) in
                       FStar_All.pipe_right uu____4284
                         (FStar_Util.map_option
                            (fun loc ->
                               let uu____4355 =
                                 let uu____4357 =
                                   assoc1 "[location]" "filename" loc in
                                 FStar_All.pipe_right uu____4357 js_str in
                               let uu____4361 =
                                 let uu____4363 =
                                   assoc1 "[location]" "line" loc in
                                 FStar_All.pipe_right uu____4363 js_int in
                               let uu____4367 =
                                 let uu____4369 =
                                   assoc1 "[location]" "column" loc in
                                 FStar_All.pipe_right uu____4369 js_int in
                               (uu____4355, uu____4361, uu____4367))) in
                     let uu____4376 =
                       let uu____4380 = arg "requested-info" in
                       FStar_All.pipe_right uu____4380 (js_list js_str) in
                     (uu____4269, uu____4274, uu____4281, uu____4376) in
                   Lookup uu____4254
               | "compute" ->
                   let uu____4393 =
                     let uu____4403 =
                       let uu____4405 = arg "term" in
                       FStar_All.pipe_right uu____4405 js_str in
                     let uu____4408 =
                       let uu____4413 = try_arg "rules" in
                       FStar_All.pipe_right uu____4413
                         (FStar_Util.map_option (js_list js_reductionrule)) in
                     (uu____4403, uu____4408) in
                   Compute uu____4393
               | "search" ->
                   let uu____4431 =
                     let uu____4433 = arg "terms" in
                     FStar_All.pipe_right uu____4433 js_str in
                   Search uu____4431
               | "vfs-add" ->
                   let uu____4437 =
                     let uu____4446 =
                       let uu____4450 = try_arg "filename" in
                       FStar_All.pipe_right uu____4450
                         (FStar_Util.map_option js_str) in
                     let uu____4460 =
                       let uu____4462 = arg "contents" in
                       FStar_All.pipe_right uu____4462 js_str in
                     (uu____4446, uu____4460) in
                   VfsAdd uu____4437
               | uu____4469 ->
                   let uu____4471 =
                     FStar_Util.format1 "Unknown query '%s'" query in
                   ProtocolViolation uu____4471 in
             { qq = uu____4178; qid }) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected, got) -> wrap_js_failure qid expected got
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query ->
    try
      (fun uu___579_4490 ->
         match () with | () -> unpack_interactive_query js_query) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected, got) -> wrap_js_failure "?" expected got
let (parse_interactive_query : Prims.string -> query) =
  fun query_str ->
    let uu____4510 = FStar_Util.json_of_string query_str in
    match uu____4510 with
    | FStar_Pervasives_Native.None ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream ->
    let uu____4522 = FStar_Util.read_line stream in
    match uu____4522 with
    | FStar_Pervasives_Native.None -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
let json_of_opt :
  'Auu____4538 .
    ('Auu____4538 -> FStar_Util.json) ->
      'Auu____4538 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a ->
    fun opt_a ->
      let uu____4558 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____4558
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
    let uu____4578 =
      let uu____4586 =
        let uu____4594 =
          let uu____4602 =
            let uu____4608 =
              let uu____4609 =
                let uu____4612 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____4618 = FStar_Range.json_of_use_range r in
                      [uu____4618] in
                let uu____4619 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____4625 = FStar_Range.def_range r in
                      let uu____4626 = FStar_Range.use_range r in
                      uu____4625 <> uu____4626 ->
                      let uu____4627 = FStar_Range.json_of_def_range r in
                      [uu____4627]
                  | uu____4628 -> [] in
                FStar_List.append uu____4612 uu____4619 in
              FStar_Util.JsonList uu____4609 in
            ("ranges", uu____4608) in
          [uu____4602] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____4594 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____4586 in
    FStar_Util.JsonAssoc uu____4578
type symbol_lookup_result =
  {
  slr_name: Prims.string ;
  slr_def_range: FStar_Range.range FStar_Pervasives_Native.option ;
  slr_typ: Prims.string FStar_Pervasives_Native.option ;
  slr_doc: Prims.string FStar_Pervasives_Native.option ;
  slr_def: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mksymbol_lookup_result__item__slr_name :
  symbol_lookup_result -> Prims.string) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_name
let (__proj__Mksymbol_lookup_result__item__slr_def_range :
  symbol_lookup_result -> FStar_Range.range FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} ->
        slr_def_range
let (__proj__Mksymbol_lookup_result__item__slr_typ :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_typ
let (__proj__Mksymbol_lookup_result__item__slr_doc :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_doc
let (__proj__Mksymbol_lookup_result__item__slr_def :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_def
let (alist_of_symbol_lookup_result :
  symbol_lookup_result -> (Prims.string * FStar_Util.json) Prims.list) =
  fun lr ->
    let uu____4846 =
      let uu____4854 =
        let uu____4860 =
          json_of_opt FStar_Range.json_of_def_range lr.slr_def_range in
        ("defined-at", uu____4860) in
      let uu____4863 =
        let uu____4871 =
          let uu____4877 =
            json_of_opt (fun _4879 -> FStar_Util.JsonStr _4879) lr.slr_typ in
          ("type", uu____4877) in
        let uu____4882 =
          let uu____4890 =
            let uu____4896 =
              json_of_opt (fun _4898 -> FStar_Util.JsonStr _4898) lr.slr_doc in
            ("documentation", uu____4896) in
          let uu____4901 =
            let uu____4909 =
              let uu____4915 =
                json_of_opt (fun _4917 -> FStar_Util.JsonStr _4917)
                  lr.slr_def in
              ("definition", uu____4915) in
            [uu____4909] in
          uu____4890 :: uu____4901 in
        uu____4871 :: uu____4882 in
      uu____4854 :: uu____4863 in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____4846
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____4962 =
      FStar_List.map (fun _4966 -> FStar_Util.JsonStr _4966)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _4969 -> FStar_Util.JsonList _4969) uu____4962 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptSet -> true | uu____4998 -> false
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReset -> true | uu____5009 -> false
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReadOnly -> true | uu____5020 -> false
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___9_5028 ->
    match uu___9_5028 with
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
  fun uu___10_5279 ->
    match uu___10_5279 with
    | FStar_Options.Const uu____5281 -> "flag"
    | FStar_Options.IntStr uu____5283 -> "int"
    | FStar_Options.BoolStr -> "bool"
    | FStar_Options.PathStr uu____5287 -> "path"
    | FStar_Options.SimpleStr uu____5290 -> "string"
    | FStar_Options.EnumStr uu____5293 -> "enum"
    | FStar_Options.OpenEnumStr uu____5298 -> "open enum"
    | FStar_Options.PostProcessed (uu____5308, typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____5318, typ) ->
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
        | FStar_Options.Const uu____5390 -> [""]
        | FStar_Options.BoolStr -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs, desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____5428, elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____5438, elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____5446 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____5446
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___11_5457 ->
    match uu___11_5457 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____5469 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____5469
    | FStar_Options.Unset -> FStar_Util.JsonNull
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt ->
    let uu____5485 =
      let uu____5493 =
        let uu____5501 =
          let uu____5507 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____5507) in
        let uu____5510 =
          let uu____5518 =
            let uu____5524 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____5524) in
          let uu____5527 =
            let uu____5535 =
              let uu____5541 =
                json_of_opt (fun _5543 -> FStar_Util.JsonStr _5543)
                  opt.opt_documentation in
              ("documentation", uu____5541) in
            let uu____5546 =
              let uu____5554 =
                let uu____5560 =
                  let uu____5561 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____5561 in
                ("type", uu____5560) in
              [uu____5554;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____5535 :: uu____5546 in
          uu____5518 :: uu____5527 in
        uu____5501 :: uu____5510 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____5493 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____5485
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt ->
    let uu____5617 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____5617
let (write_json : FStar_Util.json -> unit) =
  fun json ->
    (let uu____5632 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____5632);
    FStar_Util.print_raw "\n"
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
      fun response -> write_json (json_of_response qid status response)
let (json_of_message : Prims.string -> FStar_Util.json -> FStar_Util.json) =
  fun level ->
    fun js_contents ->
      let uu____5723 =
        let uu____5731 =
          let uu____5739 =
            let uu____5745 =
              let uu____5746 = FStar_ST.op_Bang repl_current_qid in
              json_of_opt (fun _5776 -> FStar_Util.JsonStr _5776) uu____5746 in
            ("query-id", uu____5745) in
          [uu____5739;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)] in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____5731 in
      FStar_Util.JsonAssoc uu____5723
let forward_message :
  'Auu____5820 .
    (FStar_Util.json -> 'Auu____5820) ->
      Prims.string -> FStar_Util.json -> 'Auu____5820
  =
  fun callback ->
    fun level ->
      fun contents ->
        let uu____5843 = json_of_message level contents in
        callback uu____5843
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____5847 =
      FStar_List.map (fun _5851 -> FStar_Util.JsonStr _5851)
        interactive_protocol_features in
    FStar_Util.JsonList uu____5847 in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
let (write_hello : unit -> unit) = fun uu____5865 -> write_json json_of_hello
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name ->
    fun typ ->
      let flag = Prims.op_Hat "--" name in
      let uu____5883 = FStar_Options.desc_of_opt_type typ in
      match uu____5883 with
      | FStar_Pervasives_Native.None -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____5899 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____5934 ->
            match uu____5934 with
            | (_shortname, name, typ, doc1) ->
                let uu____5958 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____5958
                  (FStar_Util.map_option
                     (fun default_value ->
                        let uu____5970 = sig_of_fstar_option name typ in
                        let uu____5972 = snippets_of_fstar_option name typ in
                        let uu____5976 =
                          let uu____5977 = FStar_Options.settable name in
                          if uu____5977
                          then OptSet
                          else
                            (let uu____5982 = FStar_Options.resettable name in
                             if uu____5982 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____5970;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____5972;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____5976
                        })))) in
  FStar_All.pipe_right uu____5899
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
    let uu___768_6021 = opt in
    let uu____6022 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___768_6021.opt_name);
      opt_sig = (uu___768_6021.opt_sig);
      opt_value = uu____6022;
      opt_default = (uu___768_6021.opt_default);
      opt_type = (uu___768_6021.opt_type);
      opt_snippets = (uu___768_6021.opt_snippets);
      opt_documentation = (uu___768_6021.opt_documentation);
      opt_permission_level = (uu___768_6021.opt_permission_level)
    }
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1 ->
    let uu____6038 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____6038
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____6065 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____6065)
    else ("", opt_name)
let (json_of_repl_state : repl_state -> FStar_Util.json) =
  fun st ->
    let filenames uu____6096 =
      match uu____6096 with
      | (uu____6108, (task, uu____6110)) ->
          (match task with
           | LDInterleaved (intf, impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | uu____6129 -> []) in
    let uu____6131 =
      let uu____6139 =
        let uu____6145 =
          let uu____6146 =
            let uu____6149 =
              FStar_List.concatMap filenames st.repl_deps_stack in
            FStar_List.map (fun _6163 -> FStar_Util.JsonStr _6163) uu____6149 in
          FStar_Util.JsonList uu____6146 in
        ("loaded-dependencies", uu____6145) in
      let uu____6166 =
        let uu____6174 =
          let uu____6180 =
            let uu____6181 =
              let uu____6184 = current_fstar_options (fun uu____6189 -> true) in
              FStar_List.map json_of_fstar_option uu____6184 in
            FStar_Util.JsonList uu____6181 in
          ("options", uu____6180) in
        [uu____6174] in
      uu____6139 :: uu____6166 in
    FStar_Util.JsonAssoc uu____6131
let with_printed_effect_args :
  'Auu____6213 . (unit -> 'Auu____6213) -> 'Auu____6213 =
  fun k ->
    FStar_Options.with_saved_options
      (fun uu____6226 ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun tcenv ->
    fun t ->
      with_printed_effect_args
        (fun uu____6244 -> FStar_TypeChecker_Normalize.term_to_string tcenv t)
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    with_printed_effect_args
      (fun uu____6254 -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit :
  'Auu____6262 'Auu____6263 .
    'Auu____6262 ->
      ((query_status * FStar_Util.json) * ('Auu____6263, Prims.int)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol :
  'Auu____6300 'Auu____6301 .
    'Auu____6300 ->
      ((query_status * FStar_Util.json) * ('Auu____6300, 'Auu____6301)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl :
  'Auu____6332 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state, 'Auu____6332)
        FStar_Util.either)
  =
  fun st ->
    let uu____6350 =
      let uu____6355 = json_of_repl_state st in (QueryOK, uu____6355) in
    (uu____6350, (FStar_Util.Inl st))
let run_protocol_violation :
  'Auu____6373 'Auu____6374 .
    'Auu____6373 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____6373, 'Auu____6374)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error :
  'Auu____6416 'Auu____6417 .
    'Auu____6416 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____6416, 'Auu____6417)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____6457 ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment :
  'Auu____6469 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____6469)
          FStar_Util.either)
  =
  fun st ->
    fun code ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
          FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
        } in
      let collect_decls uu____6504 =
        let uu____6505 = FStar_Parser_Driver.parse_fragment frag in
        match uu____6505 with
        | FStar_Parser_Driver.Empty -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____6511, decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____6517, decls, uu____6519)) -> decls in
      let uu____6526 =
        with_captured_errors st.repl_env FStar_Util.sigint_ignore
          (fun uu____6535 ->
             let uu____6536 = collect_decls () in
             FStar_All.pipe_left
               (fun _6547 -> FStar_Pervasives_Native.Some _6547) uu____6536) in
      match uu____6526 with
      | FStar_Pervasives_Native.None ->
          let errors =
            let uu____6565 = collect_errors () in
            FStar_All.pipe_right uu____6565 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____6591 =
              let uu____6599 =
                let uu____6605 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu____6605) in
              [uu____6599] in
            FStar_Util.JsonAssoc uu____6591 in
          let js_decls =
            let uu____6619 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left (fun _6624 -> FStar_Util.JsonList _6624)
              uu____6619 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add :
  'Auu____6654 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (repl_state, 'Auu____6654)
            FStar_Util.either)
  =
  fun st ->
    fun opt_fname ->
      fun contents ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop :
  'Auu____6707 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state, 'Auu____6707)
        FStar_Util.either)
  =
  fun st ->
    let uu____6725 = nothing_left_to_pop st in
    if uu____6725
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
      let uu____6812 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents) in
      write_json uu____6812
let (write_repl_ld_task_progress : repl_task -> unit) =
  fun task ->
    match task with
    | LDInterleaved (uu____6820, tf) ->
        let modname = FStar_Parser_Dep.module_name_of_file tf.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | LDSingle tf ->
        let modname = FStar_Parser_Dep.module_name_of_file tf.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | LDInterfaceOfCurrentFile tf ->
        let modname = FStar_Parser_Dep.module_name_of_file tf.tf_fname in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | uu____6872 -> ()
let (load_deps :
  repl_state ->
    ((repl_state * Prims.string Prims.list), repl_state) FStar_Util.either)
  =
  fun st ->
    let uu____6890 =
      with_captured_errors st.repl_env FStar_Util.sigint_ignore
        (fun _env ->
           let uu____6918 = deps_and_repl_ld_tasks_of_our_file st.repl_fname in
           FStar_All.pipe_left
             (fun _6965 -> FStar_Pervasives_Native.Some _6965) uu____6918) in
    match uu____6890 with
    | FStar_Pervasives_Native.None -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) ->
        let st1 =
          let uu___866_7020 = st in
          let uu____7021 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1 in
          {
            repl_line = (uu___866_7020.repl_line);
            repl_column = (uu___866_7020.repl_column);
            repl_fname = (uu___866_7020.repl_fname);
            repl_deps_stack = (uu___866_7020.repl_deps_stack);
            repl_curmod = (uu___866_7020.repl_curmod);
            repl_env = uu____7021;
            repl_stdin = (uu___866_7020.repl_stdin);
            repl_names = (uu___866_7020.repl_names)
          } in
        let uu____7022 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress in
        (match uu____7022 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue ->
    let uu___876_7077 = issue in
    let uu____7078 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____7078;
      FStar_Errors.issue_level = (uu___876_7077.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___876_7077.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___876_7077.FStar_Errors.issue_number)
    }
let run_push_without_deps :
  'Auu____7088 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____7088)
          FStar_Util.either)
  =
  fun st ->
    fun query ->
      let set_nosynth_flag st1 flag =
        let uu___883_7124 = st1 in
        {
          repl_line = (uu___883_7124.repl_line);
          repl_column = (uu___883_7124.repl_column);
          repl_fname = (uu___883_7124.repl_fname);
          repl_deps_stack = (uu___883_7124.repl_deps_stack);
          repl_curmod = (uu___883_7124.repl_curmod);
          repl_env =
            (let uu___885_7126 = st1.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___885_7126.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___885_7126.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___885_7126.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___885_7126.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___885_7126.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___885_7126.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___885_7126.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___885_7126.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___885_7126.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___885_7126.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___885_7126.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___885_7126.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___885_7126.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___885_7126.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___885_7126.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___885_7126.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___885_7126.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___885_7126.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___885_7126.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___885_7126.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___885_7126.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___885_7126.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___885_7126.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___885_7126.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___885_7126.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___885_7126.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___885_7126.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___885_7126.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___885_7126.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___885_7126.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___885_7126.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___885_7126.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___885_7126.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___885_7126.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___885_7126.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___885_7126.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___885_7126.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___885_7126.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___885_7126.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___885_7126.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___885_7126.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___885_7126.FStar_TypeChecker_Env.nbe)
             });
          repl_stdin = (uu___883_7124.repl_stdin);
          repl_names = (uu___883_7124.repl_names)
        } in
      let uu____7127 = query in
      match uu____7127 with
      | { push_kind; push_code = text; push_line = line;
          push_column = column; push_peek_only = peek_only;_} ->
          let frag =
            {
              FStar_Parser_ParseIt.frag_text = text;
              FStar_Parser_ParseIt.frag_line = line;
              FStar_Parser_ParseIt.frag_col = column
            } in
          (FStar_TypeChecker_Env.toggle_id_info st.repl_env true;
           (let st1 = set_nosynth_flag st peek_only in
            let uu____7153 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag) in
            match uu____7153 with
            | (success, st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____7182 =
                    let uu____7185 = collect_errors () in
                    FStar_All.pipe_right uu____7185
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____7182 in
                let st4 =
                  if success
                  then
                    let uu___904_7194 = st3 in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___904_7194.repl_fname);
                      repl_deps_stack = (uu___904_7194.repl_deps_stack);
                      repl_curmod = (uu___904_7194.repl_curmod);
                      repl_env = (uu___904_7194.repl_env);
                      repl_stdin = (uu___904_7194.repl_stdin);
                      repl_names = (uu___904_7194.repl_names)
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
       let uu____7224 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1")) in
       Prims.op_Hat (FStar_String.uppercase first) uu____7224)
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
          let uu____7265 = FStar_Util.psmap_empty () in
          let uu____7270 =
            let uu____7274 = FStar_Options.prims () in uu____7274 :: deps in
          FStar_List.fold_left
            (fun acc ->
               fun dep1 ->
                 let uu____7290 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____7290 true) uu____7265
            uu____7270 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1 ->
             fun uu____7319 ->
               match uu____7319 with
               | (modname, mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____7342 = capitalize modname in
                        FStar_Util.split uu____7342 "." in
                      let uu____7345 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____7345 mod_path ns_query)) table
          (FStar_List.rev mods)
let run_push_with_deps :
  'Auu____7360 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____7360)
          FStar_Util.either)
  =
  fun st ->
    fun query ->
      (let uu____7384 = FStar_Options.debug_any () in
       if uu____7384
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____7392 = load_deps st in
       match uu____7392 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____7427 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____7427 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1, deps) ->
           ((let uu____7461 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____7461 (fun a2 -> ()));
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names in
             run_push_without_deps
               (let uu___942_7465 = st1 in
                {
                  repl_line = (uu___942_7465.repl_line);
                  repl_column = (uu___942_7465.repl_column);
                  repl_fname = (uu___942_7465.repl_fname);
                  repl_deps_stack = (uu___942_7465.repl_deps_stack);
                  repl_curmod = (uu___942_7465.repl_curmod);
                  repl_env = (uu___942_7465.repl_env);
                  repl_stdin = (uu___942_7465.repl_stdin);
                  repl_names = names1
                }) query)))
let run_push :
  'Auu____7473 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____7473)
          FStar_Util.either)
  =
  fun st ->
    fun query ->
      let uu____7496 = nothing_left_to_pop st in
      if uu____7496
      then run_push_with_deps st query
      else run_push_without_deps st query
let (run_symbol_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option
        ->
        Prims.string Prims.list ->
          (Prims.string,
            (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
            FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let tcenv = st.repl_env in
          let info_of_lid_str lid_str =
            let lid =
              let uu____7604 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".") in
              FStar_Ident.lid_of_ids uu____7604 in
            let lid1 =
              let uu____7610 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____7610 in
            let uu____7615 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
            FStar_All.pipe_right uu____7615
              (FStar_Util.map_option
                 (fun uu____7672 ->
                    match uu____7672 with
                    | ((uu____7692, typ), r) ->
                        ((FStar_Util.Inr lid1), typ, r))) in
          let docs_of_lid lid =
            let uu____7714 =
              FStar_Syntax_DsEnv.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid in
            FStar_All.pipe_right uu____7714
              (FStar_Util.map_option FStar_Pervasives_Native.fst) in
          let def_of_lid lid =
            let uu____7780 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
            FStar_Util.bind_opt uu____7780
              (fun uu___12_7825 ->
                 match uu___12_7825 with
                 | (FStar_Util.Inr (se, uu____7848), uu____7849) ->
                     let uu____7878 = sigelt_to_string se in
                     FStar_Pervasives_Native.Some uu____7878
                 | uu____7881 -> FStar_Pervasives_Native.None) in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____7939 ->
                 match uu____7939 with
                 | (file, row, col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____7998 -> info_at_pos_opt
            | FStar_Pervasives_Native.None ->
                if symbol = ""
                then FStar_Pervasives_Native.None
                else info_of_lid_str symbol in
          let response =
            match info_opt with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (name_or_lid, typ, rng) ->
                let name =
                  match name_or_lid with
                  | FStar_Util.Inl name -> name
                  | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
                let typ_str =
                  if FStar_List.mem "type" requested_info
                  then
                    let uu____8155 = term_to_string tcenv typ in
                    FStar_Pervasives_Native.Some uu____8155
                  else FStar_Pervasives_Native.None in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____8172 -> FStar_Pervasives_Native.None in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____8190 -> FStar_Pervasives_Native.None in
                let def_range1 =
                  if FStar_List.mem "defined-at" requested_info
                  then FStar_Pervasives_Native.Some rng
                  else FStar_Pervasives_Native.None in
                let result =
                  {
                    slr_name = name;
                    slr_def_range = def_range1;
                    slr_typ = typ_str;
                    slr_doc = doc_str;
                    slr_def = def_str
                  } in
                let uu____8208 =
                  let uu____8221 = alist_of_symbol_lookup_result result in
                  ("symbol", uu____8221) in
                FStar_Pervasives_Native.Some uu____8208 in
          match response with
          | FStar_Pervasives_Native.None -> FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some info -> FStar_Util.Inr info
let (run_option_lookup :
  Prims.string ->
    (Prims.string,
      (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
      FStar_Util.either)
  =
  fun opt_name ->
    let uu____8356 = trim_option_name opt_name in
    match uu____8356 with
    | (uu____8380, trimmed_name) ->
        let uu____8386 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____8386 with
         | FStar_Pervasives_Native.None ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____8421 =
               let uu____8434 =
                 let uu____8442 = update_option opt in
                 alist_of_fstar_option uu____8442 in
               ("option", uu____8434) in
             FStar_Util.Inr uu____8421)
let (run_module_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string,
        (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
        FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      let query = FStar_Util.split symbol "." in
      let uu____8500 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query in
      match uu____8500 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____8535 =
            let uu____8548 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____8548) in
          FStar_Util.Inr uu____8535
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____8579 =
            let uu____8592 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____8592) in
          FStar_Util.Inr uu____8579
let (run_code_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option
        ->
        Prims.string Prims.list ->
          (Prims.string,
            (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
            FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let uu____8690 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____8690 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____8764 ->
              let uu____8779 = run_module_lookup st symbol in
              (match uu____8779 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
let (run_lookup' :
  repl_state ->
    Prims.string ->
      lookup_context ->
        (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option
          ->
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
  'Auu____8985 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string * Prims.int * Prims.int)
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) * (repl_state, 'Auu____8985)
                FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun context ->
        fun pos_opt ->
          fun requested_info ->
            let uu____9053 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____9053 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind, info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let code_autocomplete_mod_filter :
  'Auu____9157 .
    ('Auu____9157 * FStar_Interactive_CompletionTable.mod_symbol) ->
      ('Auu____9157 * FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___13_9172 ->
    match uu___13_9172 with
    | (uu____9177, FStar_Interactive_CompletionTable.Namespace uu____9178) ->
        FStar_Pervasives_Native.None
    | (uu____9183, FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____9184;
         FStar_Interactive_CompletionTable.mod_path = uu____9185;
         FStar_Interactive_CompletionTable.mod_loaded = true;_})
        -> FStar_Pervasives_Native.None
    | (pth, FStar_Interactive_CompletionTable.Module md) ->
        let uu____9195 =
          let uu____9200 =
            let uu____9201 =
              let uu___1076_9202 = md in
              let uu____9203 =
                let uu____9205 =
                  FStar_Interactive_CompletionTable.mod_name md in
                Prims.op_Hat uu____9205 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____9203;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___1076_9202.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___1076_9202.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____9201 in
          (pth, uu____9200) in
        FStar_Pervasives_Native.Some uu____9195
let run_code_autocomplete :
  'Auu____9219 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____9219)
          FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      let needle = FStar_Util.split search_term "." in
      let mods_and_nss =
        FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
          st.repl_names needle code_autocomplete_mod_filter in
      let lids =
        FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names
          needle in
      let json =
        FStar_List.map
          FStar_Interactive_CompletionTable.json_of_completion_result
          (FStar_List.append lids mods_and_nss) in
      ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let run_module_autocomplete :
  'Auu____9281 'Auu____9282 'Auu____9283 .
    repl_state ->
      Prims.string ->
        'Auu____9281 ->
          'Auu____9282 ->
            ((query_status * FStar_Util.json) * (repl_state, 'Auu____9283)
              FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun modules1 ->
        fun namespaces ->
          let needle = FStar_Util.split search_term "." in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.repl_names needle
              (fun _9330 -> FStar_Pervasives_Native.Some _9330) in
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
        let uu____9364 =
          match opt.opt_permission_level with
          | OptSet -> (true, "")
          | OptReset -> (is_reset, "#reset-only")
          | OptReadOnly -> (false, "read-only") in
        match uu____9364 with
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
  'Auu____9427 'Auu____9428 .
    'Auu____9427 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____9427, 'Auu____9428)
            FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun is_reset ->
        let uu____9460 = trim_option_name search_term in
        match uu____9460 with
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
        | (uu____9516, uu____9517) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete :
  'Auu____9540 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (repl_state, 'Auu____9540)
            FStar_Util.either)
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
  'Auu____9591 'Auu____9592 .
    repl_state ->
      'Auu____9591 ->
        (repl_state -> 'Auu____9591) ->
          ('Auu____9591 * (repl_state, 'Auu____9592) FStar_Util.either)
  =
  fun st ->
    fun sigint_default ->
      fun task ->
        let st1 = push_repl "run_and_rewind" FullCheck Noop st in
        let results =
          try
            (fun uu___1135_9633 ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____9644 ->
                        let uu____9645 = task st1 in
                        FStar_All.pipe_left
                          (fun _9650 -> FStar_Util.Inl _9650) uu____9645)) ()
          with | FStar_Util.SigInt -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e in
        let st2 = pop_repl "run_and_rewind" st1 in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
let run_with_parsed_and_tc_term :
  'Auu____9699 'Auu____9700 'Auu____9701 .
    repl_state ->
      Prims.string ->
        'Auu____9699 ->
          'Auu____9700 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) * (repl_state, 'Auu____9701)
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
                    ((uu____9802,
                      { FStar_Syntax_Syntax.lbname = uu____9803;
                        FStar_Syntax_Syntax.lbunivs = univs1;
                        FStar_Syntax_Syntax.lbtyp = uu____9805;
                        FStar_Syntax_Syntax.lbeff = uu____9806;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu____9808;
                        FStar_Syntax_Syntax.lbpos = uu____9809;_}::[]),
                     uu____9810);
                  FStar_Syntax_Syntax.sigrng = uu____9811;
                  FStar_Syntax_Syntax.sigquals = uu____9812;
                  FStar_Syntax_Syntax.sigmeta = uu____9813;
                  FStar_Syntax_Syntax.sigattrs = uu____9814;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____9853 -> FStar_Pervasives_Native.None in
            let parse1 frag =
              let uu____9874 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu____9874 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls, uu____9880) ->
                  FStar_Pervasives_Native.Some decls
              | uu____9901 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu____9919 =
                let uu____9924 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu____9924 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu____9919 in
            let typecheck tcenv decls =
              let uu____9946 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu____9946 with | (ses, uu____9960, uu____9961) -> ses in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1 ->
                 let tcenv = st1.repl_env in
                 let frag = dummy_let_fragment term in
                 let uu____9982 = parse1 frag in
                 match uu____9982 with
                 | FStar_Pervasives_Native.None ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____10008 =
                       let decls1 = desugar tcenv decls in
                       let ses = typecheck tcenv decls1 in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1, def) ->
                           let uu____10044 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def in
                           (match uu____10044 with
                            | (univs2, def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2 in
                                continuation tcenv1 def1) in
                     let uu____10056 = FStar_Options.trace_error () in
                     if uu____10056
                     then aux ()
                     else
                       (try
                          (fun uu___1218_10070 ->
                             match () with | () -> aux ()) ()
                        with
                        | uu___1217_10079 ->
                            let uu____10084 =
                              FStar_Errors.issue_of_exn uu___1217_10079 in
                            (match uu____10084 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____10092 =
                                   let uu____10093 =
                                     FStar_Errors.format_issue issue in
                                   FStar_Util.JsonStr uu____10093 in
                                 (QueryNOK, uu____10092)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Exn.raise uu___1217_10079)))
let run_compute :
  'Auu____10108 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (repl_state, 'Auu____10108)
            FStar_Util.either)
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
               let uu____10186 =
                 let uu____10187 = term_to_string tcenv normalized in
                 FStar_Util.JsonStr uu____10187 in
               (QueryOK, uu____10186))
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NameContainsStr _0 -> true | uu____10222 -> false
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee -> match projectee with | NameContainsStr _0 -> _0
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeContainsLid _0 -> true | uu____10244 -> false
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TypeContainsLid _0 -> _0
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | { st_negate; st_term;_} -> st_negate
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee -> match projectee with | { st_negate; st_term;_} -> st_term
let (st_cost : search_term' -> Prims.int) =
  fun uu___14_10279 ->
    match uu___14_10279 with
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
    let uu____10413 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____10420 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____10413; sc_fvars = uu____10420 }
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv ->
    fun sc ->
      let uu____10444 = FStar_ST.op_Bang sc.sc_typ in
      match uu____10444 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let typ =
            let uu____10472 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____10472 with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____10491, typ), uu____10493)
                -> typ in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
let (sc_fvars :
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lident FStar_Util.set)
  =
  fun tcenv ->
    fun sc ->
      let uu____10543 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____10543 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None ->
          let fv =
            let uu____10587 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____10587 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv ->
    fun sc ->
      let typ_str =
        let uu____10631 = sc_typ tcenv sc in term_to_string tcenv uu____10631 in
      let uu____10632 =
        let uu____10640 =
          let uu____10646 =
            let uu____10647 =
              let uu____10649 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              uu____10649.FStar_Ident.str in
            FStar_Util.JsonStr uu____10647 in
          ("lid", uu____10646) in
        [uu____10640; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____10632
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidSearch uu____10682 -> true
    | uu____10685 -> false
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidSearch uu____10695 -> uu____10695
let run_search :
  'Auu____10704 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____10704)
          FStar_Util.either)
  =
  fun st ->
    fun search_str ->
      let tcenv = st.repl_env in
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____10751 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____10751 in
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
              let uu____10810 =
                let uu____10811 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____10811 in
              FStar_Exn.raise uu____10810
            else
              if beg_quote
              then
                (let uu____10817 = strip_quotes term1 in
                 NameContainsStr uu____10817)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____10822 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____10822 with
                 | FStar_Pervasives_Native.None ->
                     let uu____10825 =
                       let uu____10826 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____10826 in
                     FStar_Exn.raise uu____10825
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____10854 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____10854 in
      let results =
        try
          (fun uu___1331_10888 ->
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
                        let uu____10936 = FStar_List.map pprint_one terms in
                        FStar_Util.concat_l " " uu____10936 in
                      let uu____10942 =
                        let uu____10943 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds in
                        InvalidSearch uu____10943 in
                      FStar_Exn.raise uu____10942
                  | uu____10950 -> (QueryOK, (FStar_Util.JsonList js)))) ()
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
      (results, (FStar_Util.Inl st))
let (run_query :
  repl_state ->
    query' ->
      ((query_status * FStar_Util.json) * (repl_state, Prims.int)
        FStar_Util.either))
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
let (validate_query : repl_state -> query -> query) =
  fun st ->
    fun q ->
      match q.qq with
      | Push
          { push_kind = SyntaxCheck; push_code = uu____11081;
            push_line = uu____11082; push_column = uu____11083;
            push_peek_only = false;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____11089 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____11091 -> q)
let (validate_and_run_query :
  repl_state ->
    query ->
      ((query_status * FStar_Util.json) * (repl_state, Prims.int)
        FStar_Util.either))
  =
  fun st ->
    fun query ->
      let query1 = validate_query st query in
      FStar_ST.op_Colon_Equals repl_current_qid
        (FStar_Pervasives_Native.Some (query1.qid));
      run_query st query1.qq
let (js_repl_eval :
  repl_state ->
    query -> (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either))
  =
  fun st ->
    fun query ->
      let uu____11164 = validate_and_run_query st query in
      match uu____11164 with
      | ((status, response), st_opt) ->
          let js_response = json_of_response query.qid status response in
          (js_response, st_opt)
let (js_repl_eval_js :
  repl_state ->
    FStar_Util.json ->
      (FStar_Util.json * (repl_state, Prims.int) FStar_Util.either))
  =
  fun st ->
    fun query_js ->
      let uu____11230 = deserialize_interactive_query query_js in
      js_repl_eval st uu____11230
let (js_repl_eval_str :
  repl_state ->
    Prims.string ->
      (Prims.string * (repl_state, Prims.int) FStar_Util.either))
  =
  fun st ->
    fun query_str ->
      let uu____11254 =
        let uu____11264 = parse_interactive_query query_str in
        js_repl_eval st uu____11264 in
      match uu____11254 with
      | (js_response, st_opt) ->
          let uu____11287 = FStar_Util.string_of_json js_response in
          (uu____11287, st_opt)
let (js_repl_init_opts : unit -> unit) =
  fun uu____11300 ->
    let uu____11301 = FStar_Options.parse_cmd_line () in
    match uu____11301 with
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
              | h::uu____11324::uu____11325 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____11334 -> ()))
let rec (go : repl_state -> Prims.int) =
  fun st ->
    let query = read_interactive_query st.repl_stdin in
    let uu____11347 = validate_and_run_query st query in
    match uu____11347 with
    | ((status, response), state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____11400 =
      let uu____11403 = FStar_ST.op_Bang issues in e :: uu____11403 in
    FStar_ST.op_Colon_Equals issues uu____11400 in
  let count_errors uu____11457 =
    let uu____11458 =
      let uu____11461 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____11461 in
    FStar_List.length uu____11458 in
  let report uu____11496 =
    let uu____11497 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____11497 in
  let clear1 uu____11528 = FStar_ST.op_Colon_Equals issues [] in
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
               let uu____11589 = get_json () in
               forward_message printer label uu____11589)
    }
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
let (initial_range : FStar_Range.range) =
  let uu____11603 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  let uu____11606 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  FStar_Range.mk_range "<input>" uu____11603 uu____11606
let (build_initial_repl_state : Prims.string -> repl_state) =
  fun filename ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range in
    let uu____11620 = FStar_Util.open_stdin () in
    {
      repl_line = (Prims.parse_int "1");
      repl_column = (Prims.parse_int "0");
      repl_fname = filename;
      repl_deps_stack = [];
      repl_curmod = FStar_Pervasives_Native.None;
      repl_env = env1;
      repl_stdin = uu____11620;
      repl_names = FStar_Interactive_CompletionTable.empty
    }
let interactive_mode' : 'Auu____11636 . repl_state -> 'Auu____11636 =
  fun init_st ->
    write_hello ();
    (let exit_code =
       let uu____11645 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____11645
       then
         let uu____11649 =
           let uu____11651 = FStar_Options.file_list () in
           FStar_List.hd uu____11651 in
         FStar_SMTEncoding_Solver.with_hints_db uu____11649
           (fun uu____11658 -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    install_ide_mode_hooks write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____11672 =
       let uu____11674 = FStar_Options.codegen () in
       FStar_Option.isSome uu____11674 in
     if uu____11672
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename in
     let uu____11683 = FStar_Options.trace_error () in
     if uu____11683
     then interactive_mode' init1
     else
       (try
          (fun uu___1479_11689 ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___1478_11692 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1478_11692)))