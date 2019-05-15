open Prims
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string -> (repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env ->
    fun msg ->
      let uu____55 = FStar_TypeChecker_Tc.snapshot_context env msg in
      match uu____55 with
      | (ctx_depth, env1) ->
          let uu____99 = FStar_Options.snapshot () in
          (match uu____99 with
           | (opt_depth, ()) -> ((ctx_depth, opt_depth), env1))
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver1 ->
    fun msg ->
      fun uu____145 ->
        match uu____145 with
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
    match projectee with | SyntaxCheck -> true | uu____212 -> false
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | LaxCheck -> true | uu____223 -> false
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | FullCheck -> true | uu____234 -> false
let (set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env) =
  fun env ->
    fun check_kind ->
      let uu___26_247 = env in
      let uu____248 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___26_247.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___26_247.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___26_247.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___26_247.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___26_247.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___26_247.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___26_247.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___26_247.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___26_247.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___26_247.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___26_247.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___26_247.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___26_247.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___26_247.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___26_247.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___26_247.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___26_247.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___26_247.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___26_247.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___26_247.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___26_247.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___26_247.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___26_247.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___26_247.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___26_247.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___26_247.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___26_247.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___26_247.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___26_247.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___26_247.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___26_247.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___26_247.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___26_247.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___26_247.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___26_247.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___26_247.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___26_247.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___26_247.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___26_247.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___26_247.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____248;
        FStar_TypeChecker_Env.nbe = (uu___26_247.FStar_TypeChecker_Env.nbe)
      }
let with_captured_errors' :
  'Auu____258 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____258 FStar_Pervasives_Native.option)
          -> 'Auu____258 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        try
          (fun uu___32_288 ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____294 -> f env)) ()
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
            ((let uu____312 = FStar_TypeChecker_Env.get_range env in
              FStar_Errors.log_issue uu____312
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e, msg, r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e, msg) ->
            ((let uu____342 =
                let uu____352 =
                  let uu____360 = FStar_TypeChecker_Env.get_range env in
                  (e, msg, uu____360) in
                [uu____352] in
              FStar_TypeChecker_Err.add_errors env uu____342);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop -> FStar_Pervasives_Native.None
let with_captured_errors :
  'Auu____385 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____385 FStar_Pervasives_Native.option)
          -> 'Auu____385 FStar_Pervasives_Native.option
  =
  fun env ->
    fun sigint_handler ->
      fun f ->
        let uu____412 = FStar_Options.trace_error () in
        if uu____412
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
    let uu____459 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname in
    { tf_fname = fname; tf_modtime = uu____459 }
let (dummy_tf_of_fname : Prims.string -> timed_fname) =
  fun fname -> { tf_fname = fname; tf_modtime = t0 }
let (string_of_timed_fname : timed_fname -> Prims.string) =
  fun uu____474 ->
    match uu____474 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____484 = FStar_Util.string_of_time modtime in
           FStar_Util.format2 "{ %s; %s }" fname uu____484)
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
    match projectee with | LDInterleaved _0 -> true | uu____639 -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu____670 -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____689 -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu____708 -> false
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu____726 -> false
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
      let uu____1075 = FStar_ST.op_Bang repl_stack in
      match uu____1075 with
      | [] -> failwith "Too many pops"
      | (depth, (uu____1105, st'))::stack_tl ->
          let env =
            rollback_env (st.repl_env).FStar_TypeChecker_Env.solver msg depth in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____1152 = FStar_Util.physical_equality env st'.repl_env in
            FStar_Common.runtime_assert uu____1152 "Inconsistent stack state");
           st')
let (push_repl :
  Prims.string -> push_kind -> repl_task -> repl_state -> repl_state) =
  fun msg ->
    fun push_kind ->
      fun task ->
        fun st ->
          let uu____1178 = snapshot_env st.repl_env msg in
          match uu____1178 with
          | (depth, env) ->
              ((let uu____1186 =
                  let uu____1187 = FStar_ST.op_Bang repl_stack in
                  (depth, (task, st)) :: uu____1187 in
                FStar_ST.op_Colon_Equals repl_stack uu____1186);
               (let uu___135_1248 = st in
                let uu____1249 = set_check_kind env push_kind in
                {
                  repl_line = (uu___135_1248.repl_line);
                  repl_column = (uu___135_1248.repl_column);
                  repl_fname = (uu___135_1248.repl_fname);
                  repl_deps_stack = (uu___135_1248.repl_deps_stack);
                  repl_curmod = (uu___135_1248.repl_curmod);
                  repl_env = uu____1249;
                  repl_stdin = (uu___135_1248.repl_stdin);
                  repl_names = (uu___135_1248.repl_names)
                }))
let (nothing_left_to_pop : repl_state -> Prims.bool) =
  fun st ->
    let uu____1257 =
      let uu____1258 = FStar_ST.op_Bang repl_stack in
      FStar_List.length uu____1258 in
    uu____1257 = (FStar_List.length st.repl_deps_stack)
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of (FStar_Syntax_Syntax.binding,
  FStar_TypeChecker_Env.sig_binding) FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTAlias _0 -> true | uu____1358 -> false
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee -> match projectee with | NTAlias _0 -> _0
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTOpen _0 -> true | uu____1399 -> false
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee -> match projectee with | NTOpen _0 -> _0
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTInclude _0 -> true | uu____1434 -> false
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee -> match projectee with | NTInclude _0 -> _0
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee ->
    match projectee with | NTBinding _0 -> true | uu____1469 -> false
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
              let uu____1537 = FStar_Ident.text_of_id id1 in
              let uu____1539 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                uu____1537 [] uu____1539
            else table
        | NTOpen (host, (included, kind)) ->
            if is_cur_mod host
            then
              let uu____1547 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____1547
            else table
        | NTInclude (host, included) ->
            let uu____1553 =
              if is_cur_mod host then [] else query_of_lid host in
            let uu____1558 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____1553 uu____1558
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid, uu____1570)) -> [lid]
              | FStar_Util.Inr (lids, uu____1588) -> lids
              | uu____1593 -> [] in
            FStar_List.fold_left
              (fun tbl ->
                 fun lid ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns in
                   let uu____1610 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____1610 lid) table lids
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
              let uu____1641 = FStar_Syntax_Syntax.mod_name md in
              uu____1641.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let (commit_name_tracking :
  repl_state -> name_tracking_event Prims.list -> repl_state) =
  fun st ->
    fun name_events ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events in
      let uu___195_1667 = st in
      {
        repl_line = (uu___195_1667.repl_line);
        repl_column = (uu___195_1667.repl_column);
        repl_fname = (uu___195_1667.repl_fname);
        repl_deps_stack = (uu___195_1667.repl_deps_stack);
        repl_curmod = (uu___195_1667.repl_curmod);
        repl_env = (uu___195_1667.repl_env);
        repl_stdin = (uu___195_1667.repl_stdin);
        repl_names = names1
      }
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____1683 ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____1697 =
        let uu____1700 = FStar_ST.op_Bang events in evt :: uu____1700 in
      FStar_ST.op_Colon_Equals events uu____1697 in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1 ->
             fun op ->
               let uu____1761 =
                 let uu____1762 =
                   let uu____1767 = FStar_Syntax_DsEnv.current_module dsenv1 in
                   (uu____1767, op) in
                 NTOpen uu____1762 in
               push_event uu____1761);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1 ->
             fun ns ->
               let uu____1773 =
                 let uu____1774 =
                   let uu____1779 = FStar_Syntax_DsEnv.current_module dsenv1 in
                   (uu____1779, ns) in
                 NTInclude uu____1774 in
               push_event uu____1773);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1 ->
             fun x ->
               fun l ->
                 let uu____1787 =
                   let uu____1788 =
                     let uu____1795 =
                       FStar_Syntax_DsEnv.current_module dsenv1 in
                     (uu____1795, x, l) in
                   NTAlias uu____1788 in
                 push_event uu____1787)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1800 -> fun s -> push_event (NTBinding s))
      })
let (track_name_changes :
  env_t -> (env_t * (env_t -> (env_t * name_tracking_event Prims.list)))) =
  fun env ->
    let set_hooks dshooks tchooks env1 =
      let uu____1854 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv1 ->
             let uu____1862 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks in
             ((), uu____1862)) in
      match uu____1854 with
      | ((), tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu____1864 =
      let uu____1869 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu____1870 = FStar_TypeChecker_Env.tc_hooks env in
      (uu____1869, uu____1870) in
    match uu____1864 with
    | (old_dshooks, old_tchooks) ->
        let uu____1886 = fresh_name_tracking_hooks () in
        (match uu____1886 with
         | (events, new_dshooks, new_tchooks) ->
             let uu____1921 = set_hooks new_dshooks new_tchooks env in
             (uu____1921,
               ((fun env1 ->
                   let uu____1935 = set_hooks old_dshooks old_tchooks env1 in
                   let uu____1936 =
                     let uu____1939 = FStar_ST.op_Bang events in
                     FStar_List.rev uu____1939 in
                   (uu____1935, uu____1936)))))
let (string_of_repl_task : repl_task -> Prims.string) =
  fun uu___0_1973 ->
    match uu___0_1973 with
    | LDInterleaved (intf, impl) ->
        let uu____1977 = string_of_timed_fname intf in
        let uu____1979 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1977 uu____1979
    | LDSingle intf_or_impl ->
        let uu____1983 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____1983
    | LDInterfaceOfCurrentFile intf ->
        let uu____1987 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1987
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
        let uu____2017 =
          let uu____2022 =
            let uu____2023 =
              let uu____2029 = FStar_TypeChecker_Env.dep_graph env in
              FStar_Parser_Dep.parsing_data_of uu____2029 in
            FStar_All.pipe_right modf uu____2023 in
          FStar_Universal.tc_one_file_for_ide env intf_opt modf uu____2022 in
        match uu____2017 with | (uu____2031, env1) -> env1
let (run_repl_task : optmod_t -> env_t -> repl_task -> (optmod_t * env_t)) =
  fun curmod ->
    fun env ->
      fun task ->
        match task with
        | LDInterleaved (intf, impl) ->
            let uu____2059 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname in
            (curmod, uu____2059)
        | LDSingle intf_or_impl ->
            let uu____2062 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname in
            (curmod, uu____2062)
        | LDInterfaceOfCurrentFile intf ->
            let uu____2065 =
              FStar_Universal.load_interface_decls env intf.tf_fname in
            (curmod, uu____2065)
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
            let uu____2131 = aux deps' final_tasks1 in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____2131
        | intf_or_impl::deps' ->
            let uu____2141 = aux deps' final_tasks1 in
            (LDSingle (wrap intf_or_impl)) :: uu____2141
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
      let uu____2195 = get_mod_name f in uu____2195 = our_mod_name in
    let uu____2198 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_CheckedFiles.load_parsing_data_from_cache in
    match uu____2198 with
    | (deps, dep_graph1) ->
        let uu____2227 = FStar_List.partition has_our_mod_name deps in
        (match uu____2227 with
         | (same_name, real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____2277 =
                       let uu____2279 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu____2279 in
                     if uu____2277
                     then
                       let uu____2282 =
                         let uu____2288 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.Fatal_MissingInterface, uu____2288) in
                       FStar_Errors.raise_err uu____2282
                     else ());
                    (let uu____2295 =
                       let uu____2297 =
                         FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu____2297 in
                     if uu____2295
                     then
                       let uu____2300 =
                         let uu____2306 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____2306) in
                       FStar_Errors.raise_err uu____2300
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____2316 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu____2327 =
                       let uu____2333 =
                         FStar_Util.format message [our_mod_name; mods_str] in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____2333) in
                     FStar_Errors.raise_err uu____2327);
                    []) in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
             (real_deps, tasks, dep_graph1))
let (update_task_timestamps : repl_task -> repl_task) =
  fun uu___1_2352 ->
    match uu___1_2352 with
    | LDInterleaved (intf, impl) ->
        let uu____2355 =
          let uu____2360 = tf_of_fname intf.tf_fname in
          let uu____2361 = tf_of_fname impl.tf_fname in
          (uu____2360, uu____2361) in
        LDInterleaved uu____2355
    | LDSingle intf_or_impl ->
        let uu____2363 = tf_of_fname intf_or_impl.tf_fname in
        LDSingle uu____2363
    | LDInterfaceOfCurrentFile intf ->
        let uu____2365 = tf_of_fname intf.tf_fname in
        LDInterfaceOfCurrentFile uu____2365
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
          let uu____2397 = track_name_changes st1.repl_env in
          match uu____2397 with
          | (env, finish_name_tracking) ->
              let check_success uu____2442 =
                (let uu____2445 = FStar_Errors.get_err_count () in
                 uu____2445 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback) in
              let uu____2449 =
                let uu____2457 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1 ->
                       let uu____2471 =
                         run_repl_task st1.repl_curmod env1 task in
                       FStar_All.pipe_left
                         (fun _2490 -> FStar_Pervasives_Native.Some _2490)
                         uu____2471) in
                match uu____2457 with
                | FStar_Pervasives_Native.Some (curmod, env1) when
                    check_success () -> (curmod, env1, true)
                | uu____2506 -> ((st1.repl_curmod), env, false) in
              (match uu____2449 with
               | (curmod, env1, success) ->
                   let uu____2525 = finish_name_tracking env1 in
                   (match uu____2525 with
                    | (env2, name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___335_2546 = st1 in
                              {
                                repl_line = (uu___335_2546.repl_line);
                                repl_column = (uu___335_2546.repl_column);
                                repl_fname = (uu___335_2546.repl_fname);
                                repl_deps_stack =
                                  (uu___335_2546.repl_deps_stack);
                                repl_curmod = curmod;
                                repl_env = env2;
                                repl_stdin = (uu___335_2546.repl_stdin);
                                repl_names = (uu___335_2546.repl_names)
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
          let uu____2593 = FStar_Options.debug_any () in
          if uu____2593
          then
            let uu____2596 = string_of_repl_task task in
            FStar_Util.print2 "%s %s" verb uu____2596
          else () in
        let rec revert_many st1 uu___2_2621 =
          match uu___2_2621 with
          | [] -> st1
          | (_id, (task, _st'))::entries ->
              (debug1 "Reverting" task;
               (let st' = pop_repl "run_repl_ls_transactions" st1 in
                let dep_graph1 = FStar_TypeChecker_Env.dep_graph st1.repl_env in
                let st'1 =
                  let uu___361_2674 = st' in
                  let uu____2675 =
                    FStar_TypeChecker_Env.set_dep_graph st'.repl_env
                      dep_graph1 in
                  {
                    repl_line = (uu___361_2674.repl_line);
                    repl_column = (uu___361_2674.repl_column);
                    repl_fname = (uu___361_2674.repl_fname);
                    repl_deps_stack = (uu___361_2674.repl_deps_stack);
                    repl_curmod = (uu___361_2674.repl_curmod);
                    repl_env = uu____2675;
                    repl_stdin = (uu___361_2674.repl_stdin);
                    repl_names = (uu___361_2674.repl_names)
                  } in
                revert_many st'1 entries)) in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([], []) -> FStar_Util.Inl st1
          | (task::tasks2, []) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____2728 = FStar_Options.restore_cmd_line_options false in
                FStar_All.pipe_right uu____2728 (fun a1 -> ()));
               (let timestamped_task = update_task_timestamps task in
                let push_kind =
                  let uu____2732 = FStar_Options.lax () in
                  if uu____2732 then LaxCheck else FullCheck in
                let uu____2737 =
                  run_repl_transaction st1 push_kind false timestamped_task in
                match uu____2737 with
                | (success, st2) ->
                    if success
                    then
                      let uu____2757 =
                        let uu___386_2758 = st2 in
                        let uu____2759 = FStar_ST.op_Bang repl_stack in
                        {
                          repl_line = (uu___386_2758.repl_line);
                          repl_column = (uu___386_2758.repl_column);
                          repl_fname = (uu___386_2758.repl_fname);
                          repl_deps_stack = uu____2759;
                          repl_curmod = (uu___386_2758.repl_curmod);
                          repl_env = (uu___386_2758.repl_env);
                          repl_stdin = (uu___386_2758.repl_stdin);
                          repl_names = (uu___386_2758.repl_names)
                        } in
                      aux uu____2757 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2, prev::previous1) when
              let uu____2803 = update_task_timestamps task in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____2803
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2, previous1) ->
              let uu____2820 = revert_many st1 previous1 in
              aux uu____2820 tasks2 [] in
        aux st tasks (FStar_List.rev st.repl_deps_stack)
let (js_pushkind : FStar_Util.json -> push_kind) =
  fun s ->
    let uu____2835 = FStar_JsonHelper.js_str s in
    match uu____2835 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____2840 -> FStar_JsonHelper.js_fail "push_kind" s
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s ->
    let uu____2849 = FStar_JsonHelper.js_str s in
    match uu____2849 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____2857 -> FStar_JsonHelper.js_fail "reduction rule" s
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKCode -> true | uu____2886 -> false
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKOption _0 -> true | uu____2899 -> false
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKOption _0 -> _0
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____2927 -> false
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee -> match projectee with | CKModuleOrNamespace _0 -> _0
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2965 = FStar_JsonHelper.js_str k1 in
        (match uu____2965 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____2993 ->
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
    match projectee with | LKSymbolOnly -> true | uu____3005 -> false
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKModule -> true | uu____3016 -> false
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKOption -> true | uu____3027 -> false
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKCode -> true | uu____3038 -> false
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____3051 = FStar_JsonHelper.js_str k1 in
        (match uu____3051 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____3061 ->
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
  fun projectee -> match projectee with | Exit -> true | uu____3178 -> false
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeProtocol -> true | uu____3189 -> false
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeRepl -> true | uu____3200 -> false
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Segment _0 -> true | uu____3213 -> false
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Segment _0 -> _0
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu____3234 -> false
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Push _0 -> true | uu____3246 -> false
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | VfsAdd _0 -> true | uu____3273 -> false
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee -> match projectee with | VfsAdd _0 -> _0
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | AutoComplete _0 -> true | uu____3321 -> false
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee -> match projectee with | AutoComplete _0 -> _0
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Lookup _0 -> true | uu____3369 -> false
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee -> match projectee with | Lookup _0 -> _0
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Compute _0 -> true | uu____3439 -> false
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Compute _0 -> _0
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Search _0 -> true | uu____3486 -> false
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Search _0 -> _0
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | GenericError _0 -> true | uu____3509 -> false
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | GenericError _0 -> _0
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | ProtocolViolation _0 -> true | uu____3532 -> false
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | ProtocolViolation _0 -> _0
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___3_3570 ->
    match uu___3_3570 with
    | Exit -> false
    | DescribeProtocol -> false
    | DescribeRepl -> false
    | Segment uu____3575 -> false
    | Pop -> false
    | Push
        { push_kind = uu____3579; push_code = uu____3580;
          push_line = uu____3581; push_column = uu____3582;
          push_peek_only = false;_}
        -> false
    | VfsAdd uu____3588 -> false
    | GenericError uu____3598 -> false
    | ProtocolViolation uu____3601 -> false
    | Push uu____3604 -> true
    | AutoComplete uu____3606 -> true
    | Lookup uu____3613 -> true
    | Compute uu____3629 -> true
    | Search uu____3640 -> true
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
    match projectee with | QueryOK -> true | uu____3702 -> false
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryNOK -> true | uu____3713 -> false
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with
    | QueryViolatesProtocol -> true
    | uu____3724 -> false
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____3746 =
          let uu____3747 =
            let uu____3749 = FStar_JsonHelper.json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____3749 in
          ProtocolViolation uu____3747 in
        { qq = uu____3746; qid }
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json ->
    let assoc1 errloc key a =
      let uu____3792 = FStar_JsonHelper.try_assoc key a in
      match uu____3792 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____3796 =
            let uu____3797 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            FStar_JsonHelper.InvalidQuery uu____3797 in
          FStar_Exn.raise uu____3796 in
    let request = FStar_All.pipe_right json FStar_JsonHelper.js_assoc in
    let qid =
      let uu____3817 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____3817 FStar_JsonHelper.js_str in
    try
      (fun uu___499_3827 ->
         match () with
         | () ->
             let query =
               let uu____3830 = assoc1 "query" "query" request in
               FStar_All.pipe_right uu____3830 FStar_JsonHelper.js_str in
             let args =
               let uu____3842 = assoc1 "query" "args" request in
               FStar_All.pipe_right uu____3842 FStar_JsonHelper.js_assoc in
             let arg1 k = assoc1 "[args]" k args in
             let try_arg k =
               let uu____3871 = FStar_JsonHelper.try_assoc k args in
               match uu____3871 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull) ->
                   FStar_Pervasives_Native.None
               | other -> other in
             let uu____3879 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____3885 =
                     let uu____3887 = arg1 "code" in
                     FStar_All.pipe_right uu____3887 FStar_JsonHelper.js_str in
                   Segment uu____3885
               | "peek" ->
                   let uu____3891 =
                     let uu____3892 =
                       let uu____3893 = arg1 "kind" in
                       FStar_All.pipe_right uu____3893 js_pushkind in
                     let uu____3895 =
                       let uu____3897 = arg1 "code" in
                       FStar_All.pipe_right uu____3897
                         FStar_JsonHelper.js_str in
                     let uu____3900 =
                       let uu____3902 = arg1 "line" in
                       FStar_All.pipe_right uu____3902
                         FStar_JsonHelper.js_int in
                     let uu____3905 =
                       let uu____3907 = arg1 "column" in
                       FStar_All.pipe_right uu____3907
                         FStar_JsonHelper.js_int in
                     {
                       push_kind = uu____3892;
                       push_code = uu____3895;
                       push_line = uu____3900;
                       push_column = uu____3905;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____3891
               | "push" ->
                   let uu____3913 =
                     let uu____3914 =
                       let uu____3915 = arg1 "kind" in
                       FStar_All.pipe_right uu____3915 js_pushkind in
                     let uu____3917 =
                       let uu____3919 = arg1 "code" in
                       FStar_All.pipe_right uu____3919
                         FStar_JsonHelper.js_str in
                     let uu____3922 =
                       let uu____3924 = arg1 "line" in
                       FStar_All.pipe_right uu____3924
                         FStar_JsonHelper.js_int in
                     let uu____3927 =
                       let uu____3929 = arg1 "column" in
                       FStar_All.pipe_right uu____3929
                         FStar_JsonHelper.js_int in
                     {
                       push_kind = uu____3914;
                       push_code = uu____3917;
                       push_line = uu____3922;
                       push_column = uu____3927;
                       push_peek_only = (query = "peek")
                     } in
                   Push uu____3913
               | "autocomplete" ->
                   let uu____3935 =
                     let uu____3941 =
                       let uu____3943 = arg1 "partial-symbol" in
                       FStar_All.pipe_right uu____3943
                         FStar_JsonHelper.js_str in
                     let uu____3946 =
                       let uu____3947 = try_arg "context" in
                       FStar_All.pipe_right uu____3947
                         js_optional_completion_context in
                     (uu____3941, uu____3946) in
                   AutoComplete uu____3935
               | "lookup" ->
                   let uu____3955 =
                     let uu____3970 =
                       let uu____3972 = arg1 "symbol" in
                       FStar_All.pipe_right uu____3972
                         FStar_JsonHelper.js_str in
                     let uu____3975 =
                       let uu____3976 = try_arg "context" in
                       FStar_All.pipe_right uu____3976
                         js_optional_lookup_context in
                     let uu____3982 =
                       let uu____3985 =
                         let uu____3995 = try_arg "location" in
                         FStar_All.pipe_right uu____3995
                           (FStar_Util.map_option FStar_JsonHelper.js_assoc) in
                       FStar_All.pipe_right uu____3985
                         (FStar_Util.map_option
                            (fun loc ->
                               let uu____4056 =
                                 let uu____4058 =
                                   assoc1 "[location]" "filename" loc in
                                 FStar_All.pipe_right uu____4058
                                   FStar_JsonHelper.js_str in
                               let uu____4062 =
                                 let uu____4064 =
                                   assoc1 "[location]" "line" loc in
                                 FStar_All.pipe_right uu____4064
                                   FStar_JsonHelper.js_int in
                               let uu____4068 =
                                 let uu____4070 =
                                   assoc1 "[location]" "column" loc in
                                 FStar_All.pipe_right uu____4070
                                   FStar_JsonHelper.js_int in
                               (uu____4056, uu____4062, uu____4068))) in
                     let uu____4077 =
                       let uu____4081 = arg1 "requested-info" in
                       FStar_All.pipe_right uu____4081
                         (FStar_JsonHelper.js_list FStar_JsonHelper.js_str) in
                     (uu____3970, uu____3975, uu____3982, uu____4077) in
                   Lookup uu____3955
               | "compute" ->
                   let uu____4094 =
                     let uu____4104 =
                       let uu____4106 = arg1 "term" in
                       FStar_All.pipe_right uu____4106
                         FStar_JsonHelper.js_str in
                     let uu____4109 =
                       let uu____4114 = try_arg "rules" in
                       FStar_All.pipe_right uu____4114
                         (FStar_Util.map_option
                            (FStar_JsonHelper.js_list js_reductionrule)) in
                     (uu____4104, uu____4109) in
                   Compute uu____4094
               | "search" ->
                   let uu____4132 =
                     let uu____4134 = arg1 "terms" in
                     FStar_All.pipe_right uu____4134 FStar_JsonHelper.js_str in
                   Search uu____4132
               | "vfs-add" ->
                   let uu____4138 =
                     let uu____4147 =
                       let uu____4151 = try_arg "filename" in
                       FStar_All.pipe_right uu____4151
                         (FStar_Util.map_option FStar_JsonHelper.js_str) in
                     let uu____4161 =
                       let uu____4163 = arg1 "contents" in
                       FStar_All.pipe_right uu____4163
                         FStar_JsonHelper.js_str in
                     (uu____4147, uu____4161) in
                   VfsAdd uu____4138
               | uu____4170 ->
                   let uu____4172 =
                     FStar_Util.format1 "Unknown query '%s'" query in
                   ProtocolViolation uu____4172 in
             { qq = uu____3879; qid }) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure qid expected got
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query ->
    try
      (fun uu___534_4191 ->
         match () with | () -> unpack_interactive_query js_query) ()
    with
    | FStar_JsonHelper.InvalidQuery msg ->
        { qq = (ProtocolViolation msg); qid = "?" }
    | FStar_JsonHelper.UnexpectedJsonType (expected, got) ->
        wrap_js_failure "?" expected got
let (parse_interactive_query : Prims.string -> query) =
  fun query_str ->
    let uu____4211 = FStar_Util.json_of_string query_str in
    match uu____4211 with
    | FStar_Pervasives_Native.None ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream ->
    let uu____4223 = FStar_Util.read_line stream in
    match uu____4223 with
    | FStar_Pervasives_Native.None -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
let json_of_opt :
  'Auu____4239 .
    ('Auu____4239 -> FStar_Util.json) ->
      'Auu____4239 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a ->
    fun opt_a ->
      let uu____4259 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____4259
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
    let uu____4279 =
      let uu____4287 =
        let uu____4295 =
          let uu____4303 =
            let uu____4309 =
              let uu____4310 =
                let uu____4313 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____4319 = FStar_Range.json_of_use_range r in
                      [uu____4319] in
                let uu____4320 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____4326 = FStar_Range.def_range r in
                      let uu____4327 = FStar_Range.use_range r in
                      uu____4326 <> uu____4327 ->
                      let uu____4328 = FStar_Range.json_of_def_range r in
                      [uu____4328]
                  | uu____4329 -> [] in
                FStar_List.append uu____4313 uu____4320 in
              FStar_Util.JsonList uu____4310 in
            ("ranges", uu____4309) in
          [uu____4303] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____4295 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____4287 in
    FStar_Util.JsonAssoc uu____4279
let (alist_of_symbol_lookup_result :
  FStar_QueryHelper.sl_reponse -> (Prims.string * FStar_Util.json) Prims.list)
  =
  fun lr ->
    let uu____4371 =
      let uu____4379 =
        let uu____4385 =
          json_of_opt FStar_Range.json_of_def_range
            lr.FStar_QueryHelper.slr_def_range in
        ("defined-at", uu____4385) in
      let uu____4388 =
        let uu____4396 =
          let uu____4402 =
            json_of_opt (fun _4404 -> FStar_Util.JsonStr _4404)
              lr.FStar_QueryHelper.slr_typ in
          ("type", uu____4402) in
        let uu____4407 =
          let uu____4415 =
            let uu____4421 =
              json_of_opt (fun _4423 -> FStar_Util.JsonStr _4423)
                lr.FStar_QueryHelper.slr_doc in
            ("documentation", uu____4421) in
          let uu____4426 =
            let uu____4434 =
              let uu____4440 =
                json_of_opt (fun _4442 -> FStar_Util.JsonStr _4442)
                  lr.FStar_QueryHelper.slr_def in
              ("definition", uu____4440) in
            [uu____4434] in
          uu____4415 :: uu____4426 in
        uu____4396 :: uu____4407 in
      uu____4379 :: uu____4388 in
    ("name", (FStar_Util.JsonStr (lr.FStar_QueryHelper.slr_name))) ::
      uu____4371
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____4487 =
      FStar_List.map (fun _4491 -> FStar_Util.JsonStr _4491)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _4494 -> FStar_Util.JsonList _4494) uu____4487 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptSet -> true | uu____4523 -> false
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReset -> true | uu____4534 -> false
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee ->
    match projectee with | OptReadOnly -> true | uu____4545 -> false
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___4_4553 ->
    match uu___4_4553 with
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
  fun uu___5_4804 ->
    match uu___5_4804 with
    | FStar_Options.Const uu____4806 -> "flag"
    | FStar_Options.IntStr uu____4808 -> "int"
    | FStar_Options.BoolStr -> "bool"
    | FStar_Options.PathStr uu____4812 -> "path"
    | FStar_Options.SimpleStr uu____4815 -> "string"
    | FStar_Options.EnumStr uu____4818 -> "enum"
    | FStar_Options.OpenEnumStr uu____4823 -> "open enum"
    | FStar_Options.PostProcessed (uu____4833, typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____4843, typ) ->
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
        | FStar_Options.Const uu____4915 -> [""]
        | FStar_Options.BoolStr -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs, desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____4953, elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____4963, elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____4971 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____4971
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___6_4982 ->
    match uu___6_4982 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____4994 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____4994
    | FStar_Options.Unset -> FStar_Util.JsonNull
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt ->
    let uu____5010 =
      let uu____5018 =
        let uu____5026 =
          let uu____5032 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____5032) in
        let uu____5035 =
          let uu____5043 =
            let uu____5049 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____5049) in
          let uu____5052 =
            let uu____5060 =
              let uu____5066 =
                json_of_opt (fun _5068 -> FStar_Util.JsonStr _5068)
                  opt.opt_documentation in
              ("documentation", uu____5066) in
            let uu____5071 =
              let uu____5079 =
                let uu____5085 =
                  let uu____5086 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____5086 in
                ("type", uu____5085) in
              [uu____5079;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____5060 :: uu____5071 in
          uu____5043 :: uu____5052 in
        uu____5026 :: uu____5035 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____5018 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____5010
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt ->
    let uu____5142 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____5142
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
      let uu____5238 =
        let uu____5246 =
          let uu____5254 =
            let uu____5260 =
              let uu____5261 = FStar_ST.op_Bang repl_current_qid in
              json_of_opt (fun _5291 -> FStar_Util.JsonStr _5291) uu____5261 in
            ("query-id", uu____5260) in
          [uu____5254;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)] in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____5246 in
      FStar_Util.JsonAssoc uu____5238
let forward_message :
  'Auu____5335 .
    (FStar_Util.json -> 'Auu____5335) ->
      Prims.string -> FStar_Util.json -> 'Auu____5335
  =
  fun callback ->
    fun level ->
      fun contents ->
        let uu____5358 = json_of_message level contents in
        callback uu____5358
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____5362 =
      FStar_List.map (fun _5366 -> FStar_Util.JsonStr _5366)
        interactive_protocol_features in
    FStar_Util.JsonList uu____5362 in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
let (write_hello : unit -> unit) =
  fun uu____5380 -> FStar_JsonHelper.write_json json_of_hello
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name ->
    fun typ ->
      let flag = Prims.op_Hat "--" name in
      let uu____5398 = FStar_Options.desc_of_opt_type typ in
      match uu____5398 with
      | FStar_Pervasives_Native.None -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____5414 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____5449 ->
            match uu____5449 with
            | (_shortname, name, typ, doc1) ->
                let uu____5473 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____5473
                  (FStar_Util.map_option
                     (fun default_value ->
                        let uu____5485 = sig_of_fstar_option name typ in
                        let uu____5487 = snippets_of_fstar_option name typ in
                        let uu____5491 =
                          let uu____5492 = FStar_Options.settable name in
                          if uu____5492
                          then OptSet
                          else
                            (let uu____5497 = FStar_Options.resettable name in
                             if uu____5497 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____5485;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____5487;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____5491
                        })))) in
  FStar_All.pipe_right uu____5414
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
    let uu___706_5536 = opt in
    let uu____5537 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___706_5536.opt_name);
      opt_sig = (uu___706_5536.opt_sig);
      opt_value = uu____5537;
      opt_default = (uu___706_5536.opt_default);
      opt_type = (uu___706_5536.opt_type);
      opt_snippets = (uu___706_5536.opt_snippets);
      opt_documentation = (uu___706_5536.opt_documentation);
      opt_permission_level = (uu___706_5536.opt_permission_level)
    }
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1 ->
    let uu____5553 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____5553
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____5580 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____5580)
    else ("", opt_name)
let (json_of_repl_state : repl_state -> FStar_Util.json) =
  fun st ->
    let filenames uu____5611 =
      match uu____5611 with
      | (uu____5623, (task, uu____5625)) ->
          (match task with
           | LDInterleaved (intf, impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | uu____5644 -> []) in
    let uu____5646 =
      let uu____5654 =
        let uu____5660 =
          let uu____5661 =
            let uu____5664 =
              FStar_List.concatMap filenames st.repl_deps_stack in
            FStar_List.map (fun _5678 -> FStar_Util.JsonStr _5678) uu____5664 in
          FStar_Util.JsonList uu____5661 in
        ("loaded-dependencies", uu____5660) in
      let uu____5681 =
        let uu____5689 =
          let uu____5695 =
            let uu____5696 =
              let uu____5699 = current_fstar_options (fun uu____5704 -> true) in
              FStar_List.map json_of_fstar_option uu____5699 in
            FStar_Util.JsonList uu____5696 in
          ("options", uu____5695) in
        [uu____5689] in
      uu____5654 :: uu____5681 in
    FStar_Util.JsonAssoc uu____5646
let run_exit :
  'Auu____5730 'Auu____5731 .
    'Auu____5730 ->
      ((query_status * FStar_Util.json) * ('Auu____5731, Prims.int)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol :
  'Auu____5768 'Auu____5769 .
    'Auu____5768 ->
      ((query_status * FStar_Util.json) * ('Auu____5768, 'Auu____5769)
        FStar_Util.either)
  =
  fun st ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl :
  'Auu____5800 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state, 'Auu____5800)
        FStar_Util.either)
  =
  fun st ->
    let uu____5818 =
      let uu____5823 = json_of_repl_state st in (QueryOK, uu____5823) in
    (uu____5818, (FStar_Util.Inl st))
let run_protocol_violation :
  'Auu____5841 'Auu____5842 .
    'Auu____5841 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____5841, 'Auu____5842)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error :
  'Auu____5884 'Auu____5885 .
    'Auu____5884 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____5884, 'Auu____5885)
          FStar_Util.either)
  =
  fun st ->
    fun message ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____5925 ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment :
  'Auu____5937 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____5937)
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
      let collect_decls uu____5972 =
        let uu____5973 = FStar_Parser_Driver.parse_fragment frag in
        match uu____5973 with
        | FStar_Parser_Driver.Empty -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____5979, decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____5985, decls, uu____5987)) -> decls in
      let uu____5994 =
        with_captured_errors st.repl_env FStar_Util.sigint_ignore
          (fun uu____6003 ->
             let uu____6004 = collect_decls () in
             FStar_All.pipe_left
               (fun _6015 -> FStar_Pervasives_Native.Some _6015) uu____6004) in
      match uu____5994 with
      | FStar_Pervasives_Native.None ->
          let errors =
            let uu____6033 = collect_errors () in
            FStar_All.pipe_right uu____6033 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____6059 =
              let uu____6067 =
                let uu____6073 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu____6073) in
              [uu____6067] in
            FStar_Util.JsonAssoc uu____6059 in
          let js_decls =
            let uu____6087 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left (fun _6092 -> FStar_Util.JsonList _6092)
              uu____6087 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add :
  'Auu____6122 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (repl_state, 'Auu____6122)
            FStar_Util.either)
  =
  fun st ->
    fun opt_fname ->
      fun contents ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop :
  'Auu____6175 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state, 'Auu____6175)
        FStar_Util.either)
  =
  fun st ->
    let uu____6193 = nothing_left_to_pop st in
    if uu____6193
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
      let uu____6280 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents) in
      FStar_JsonHelper.write_json uu____6280
let (write_repl_ld_task_progress : repl_task -> unit) =
  fun task ->
    match task with
    | LDInterleaved (uu____6288, tf) ->
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
    | uu____6340 -> ()
let (load_deps :
  repl_state ->
    ((repl_state * Prims.string Prims.list), repl_state) FStar_Util.either)
  =
  fun st ->
    let uu____6358 =
      with_captured_errors st.repl_env FStar_Util.sigint_ignore
        (fun _env ->
           let uu____6386 = deps_and_repl_ld_tasks_of_our_file st.repl_fname in
           FStar_All.pipe_left
             (fun _6433 -> FStar_Pervasives_Native.Some _6433) uu____6386) in
    match uu____6358 with
    | FStar_Pervasives_Native.None -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps, tasks, dep_graph1) ->
        let st1 =
          let uu___796_6488 = st in
          let uu____6489 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1 in
          {
            repl_line = (uu___796_6488.repl_line);
            repl_column = (uu___796_6488.repl_column);
            repl_fname = (uu___796_6488.repl_fname);
            repl_deps_stack = (uu___796_6488.repl_deps_stack);
            repl_curmod = (uu___796_6488.repl_curmod);
            repl_env = uu____6489;
            repl_stdin = (uu___796_6488.repl_stdin);
            repl_names = (uu___796_6488.repl_names)
          } in
        let uu____6490 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress in
        (match uu____6490 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue ->
    let uu___806_6545 = issue in
    let uu____6546 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____6546;
      FStar_Errors.issue_level = (uu___806_6545.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___806_6545.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___806_6545.FStar_Errors.issue_number)
    }
let run_push_without_deps :
  'Auu____6556 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____6556)
          FStar_Util.either)
  =
  fun st ->
    fun query ->
      let set_nosynth_flag st1 flag =
        let uu___813_6592 = st1 in
        {
          repl_line = (uu___813_6592.repl_line);
          repl_column = (uu___813_6592.repl_column);
          repl_fname = (uu___813_6592.repl_fname);
          repl_deps_stack = (uu___813_6592.repl_deps_stack);
          repl_curmod = (uu___813_6592.repl_curmod);
          repl_env =
            (let uu___815_6594 = st1.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___815_6594.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___815_6594.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___815_6594.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___815_6594.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___815_6594.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___815_6594.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___815_6594.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___815_6594.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___815_6594.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___815_6594.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___815_6594.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___815_6594.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___815_6594.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___815_6594.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___815_6594.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___815_6594.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___815_6594.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___815_6594.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___815_6594.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___815_6594.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___815_6594.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___815_6594.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___815_6594.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___815_6594.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___815_6594.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___815_6594.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___815_6594.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___815_6594.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___815_6594.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___815_6594.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___815_6594.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___815_6594.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___815_6594.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___815_6594.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___815_6594.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___815_6594.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___815_6594.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___815_6594.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___815_6594.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___815_6594.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___815_6594.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___815_6594.FStar_TypeChecker_Env.nbe)
             });
          repl_stdin = (uu___813_6592.repl_stdin);
          repl_names = (uu___813_6592.repl_names)
        } in
      let uu____6595 = query in
      match uu____6595 with
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
            let uu____6621 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag) in
            match uu____6621 with
            | (success, st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____6650 =
                    let uu____6653 = collect_errors () in
                    FStar_All.pipe_right uu____6653
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____6650 in
                let st4 =
                  if success
                  then
                    let uu___834_6662 = st3 in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___834_6662.repl_fname);
                      repl_deps_stack = (uu___834_6662.repl_deps_stack);
                      repl_curmod = (uu___834_6662.repl_curmod);
                      repl_env = (uu___834_6662.repl_env);
                      repl_stdin = (uu___834_6662.repl_stdin);
                      repl_names = (uu___834_6662.repl_names)
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
       let uu____6692 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1")) in
       Prims.op_Hat (FStar_String.uppercase first) uu____6692)
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
          let uu____6733 = FStar_Util.psmap_empty () in
          let uu____6738 =
            let uu____6742 = FStar_Options.prims () in uu____6742 :: deps in
          FStar_List.fold_left
            (fun acc ->
               fun dep1 ->
                 let uu____6758 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____6758 true) uu____6733
            uu____6738 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1 ->
             fun uu____6787 ->
               match uu____6787 with
               | (modname, mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____6810 = capitalize modname in
                        FStar_Util.split uu____6810 "." in
                      let uu____6813 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____6813 mod_path ns_query)) table
          (FStar_List.rev mods)
let run_push_with_deps :
  'Auu____6828 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____6828)
          FStar_Util.either)
  =
  fun st ->
    fun query ->
      (let uu____6852 = FStar_Options.debug_any () in
       if uu____6852
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____6860 = load_deps st in
       match uu____6860 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____6895 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____6895 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1, deps) ->
           ((let uu____6929 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____6929 (fun a2 -> ()));
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names in
             run_push_without_deps
               (let uu___872_6933 = st1 in
                {
                  repl_line = (uu___872_6933.repl_line);
                  repl_column = (uu___872_6933.repl_column);
                  repl_fname = (uu___872_6933.repl_fname);
                  repl_deps_stack = (uu___872_6933.repl_deps_stack);
                  repl_curmod = (uu___872_6933.repl_curmod);
                  repl_env = (uu___872_6933.repl_env);
                  repl_stdin = (uu___872_6933.repl_stdin);
                  repl_names = names1
                }) query)))
let run_push :
  'Auu____6941 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____6941)
          FStar_Util.either)
  =
  fun st ->
    fun query ->
      let uu____6964 = nothing_left_to_pop st in
      if uu____6964
      then run_push_with_deps st query
      else run_push_without_deps st query
let (run_symbol_lookup :
  repl_state ->
    Prims.string ->
      FStar_QueryHelper.loc FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,
            (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
            FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let uu____7031 =
            FStar_QueryHelper.symlookup st.repl_env symbol pos_opt
              requested_info in
          match uu____7031 with
          | FStar_Pervasives_Native.None -> FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some result ->
              let uu____7066 =
                let uu____7079 = alist_of_symbol_lookup_result result in
                ("symbol", uu____7079) in
              FStar_Util.Inr uu____7066
let (run_option_lookup :
  Prims.string ->
    (Prims.string,
      (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
      FStar_Util.either)
  =
  fun opt_name ->
    let uu____7134 = trim_option_name opt_name in
    match uu____7134 with
    | (uu____7158, trimmed_name) ->
        let uu____7164 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____7164 with
         | FStar_Pervasives_Native.None ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____7199 =
               let uu____7212 =
                 let uu____7220 = update_option opt in
                 alist_of_fstar_option uu____7220 in
               ("option", uu____7212) in
             FStar_Util.Inr uu____7199)
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
      let uu____7278 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query in
      match uu____7278 with
      | FStar_Pervasives_Native.None ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____7313 =
            let uu____7326 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____7326) in
          FStar_Util.Inr uu____7313
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____7357 =
            let uu____7370 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____7370) in
          FStar_Util.Inr uu____7357
let (run_code_lookup :
  repl_state ->
    Prims.string ->
      FStar_QueryHelper.loc FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,
            (Prims.string * (Prims.string * FStar_Util.json) Prims.list))
            FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let uu____7450 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____7450 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____7524 ->
              let uu____7539 = run_module_lookup st symbol in
              (match uu____7539 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
let (run_lookup' :
  repl_state ->
    Prims.string ->
      lookup_context ->
        FStar_QueryHelper.loc FStar_Pervasives_Native.option ->
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
  'Auu____7727 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          FStar_QueryHelper.loc FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) * (repl_state, 'Auu____7727)
                FStar_Util.either)
  =
  fun st ->
    fun symbol ->
      fun context ->
        fun pos_opt ->
          fun requested_info ->
            let uu____7777 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____7777 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind, info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let code_autocomplete_mod_filter :
  'Auu____7881 .
    ('Auu____7881 * FStar_Interactive_CompletionTable.mod_symbol) ->
      ('Auu____7881 * FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___7_7896 ->
    match uu___7_7896 with
    | (uu____7901, FStar_Interactive_CompletionTable.Namespace uu____7902) ->
        FStar_Pervasives_Native.None
    | (uu____7907, FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____7908;
         FStar_Interactive_CompletionTable.mod_path = uu____7909;
         FStar_Interactive_CompletionTable.mod_loaded = true;_})
        -> FStar_Pervasives_Native.None
    | (pth, FStar_Interactive_CompletionTable.Module md) ->
        let uu____7919 =
          let uu____7924 =
            let uu____7925 =
              let uu___949_7926 = md in
              let uu____7927 =
                let uu____7929 =
                  FStar_Interactive_CompletionTable.mod_name md in
                Prims.op_Hat uu____7929 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____7927;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___949_7926.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___949_7926.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____7925 in
          (pth, uu____7924) in
        FStar_Pervasives_Native.Some uu____7919
let run_code_autocomplete :
  'Auu____7943 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____7943)
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
  'Auu____8005 'Auu____8006 'Auu____8007 .
    repl_state ->
      Prims.string ->
        'Auu____8005 ->
          'Auu____8006 ->
            ((query_status * FStar_Util.json) * (repl_state, 'Auu____8007)
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
              (fun _8054 -> FStar_Pervasives_Native.Some _8054) in
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
        let uu____8088 =
          match opt.opt_permission_level with
          | OptSet -> (true, "")
          | OptReset -> (is_reset, "#reset-only")
          | OptReadOnly -> (false, "read-only") in
        match uu____8088 with
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
  'Auu____8151 'Auu____8152 .
    'Auu____8151 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____8151, 'Auu____8152)
            FStar_Util.either)
  =
  fun st ->
    fun search_term ->
      fun is_reset ->
        let uu____8184 = trim_option_name search_term in
        match uu____8184 with
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
        | (uu____8240, uu____8241) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete :
  'Auu____8264 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (repl_state, 'Auu____8264)
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
  'Auu____8315 'Auu____8316 .
    repl_state ->
      'Auu____8315 ->
        (repl_state -> 'Auu____8315) ->
          ('Auu____8315 * (repl_state, 'Auu____8316) FStar_Util.either)
  =
  fun st ->
    fun sigint_default ->
      fun task ->
        let st1 = push_repl "run_and_rewind" FullCheck Noop st in
        let results =
          try
            (fun uu___1008_8357 ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____8368 ->
                        let uu____8369 = task st1 in
                        FStar_All.pipe_left
                          (fun _8374 -> FStar_Util.Inl _8374) uu____8369)) ()
          with | FStar_Util.SigInt -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e in
        let st2 = pop_repl "run_and_rewind" st1 in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
let run_with_parsed_and_tc_term :
  'Auu____8423 'Auu____8424 'Auu____8425 .
    repl_state ->
      Prims.string ->
        'Auu____8423 ->
          'Auu____8424 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) * (repl_state, 'Auu____8425)
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
                    ((uu____8526,
                      { FStar_Syntax_Syntax.lbname = uu____8527;
                        FStar_Syntax_Syntax.lbunivs = univs1;
                        FStar_Syntax_Syntax.lbtyp = uu____8529;
                        FStar_Syntax_Syntax.lbeff = uu____8530;
                        FStar_Syntax_Syntax.lbdef = def;
                        FStar_Syntax_Syntax.lbattrs = uu____8532;
                        FStar_Syntax_Syntax.lbpos = uu____8533;_}::[]),
                     uu____8534);
                  FStar_Syntax_Syntax.sigrng = uu____8535;
                  FStar_Syntax_Syntax.sigquals = uu____8536;
                  FStar_Syntax_Syntax.sigmeta = uu____8537;
                  FStar_Syntax_Syntax.sigattrs = uu____8538;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____8577 -> FStar_Pervasives_Native.None in
            let parse1 frag =
              let uu____8598 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu____8598 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls, uu____8604) ->
                  FStar_Pervasives_Native.Some decls
              | uu____8625 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu____8643 =
                let uu____8648 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu____8648 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu____8643 in
            let typecheck tcenv decls =
              let uu____8670 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu____8670 with | (ses, uu____8684, uu____8685) -> ses in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1 ->
                 let tcenv = st1.repl_env in
                 let frag = dummy_let_fragment term in
                 let uu____8706 = parse1 frag in
                 match uu____8706 with
                 | FStar_Pervasives_Native.None ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____8732 =
                       let decls1 = desugar tcenv decls in
                       let ses = typecheck tcenv decls1 in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1, def) ->
                           let uu____8768 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def in
                           (match uu____8768 with
                            | (univs2, def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2 in
                                continuation tcenv1 def1) in
                     let uu____8780 = FStar_Options.trace_error () in
                     if uu____8780
                     then aux ()
                     else
                       (try
                          (fun uu___1091_8794 -> match () with | () -> aux ())
                            ()
                        with
                        | uu___1090_8803 ->
                            let uu____8808 =
                              FStar_Errors.issue_of_exn uu___1090_8803 in
                            (match uu____8808 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____8816 =
                                   let uu____8817 =
                                     FStar_Errors.format_issue issue in
                                   FStar_Util.JsonStr uu____8817 in
                                 (QueryNOK, uu____8816)
                             | FStar_Pervasives_Native.None ->
                                 FStar_Exn.raise uu___1090_8803)))
let run_compute :
  'Auu____8832 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (repl_state, 'Auu____8832)
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
               let uu____8910 =
                 let uu____8911 =
                   FStar_QueryHelper.term_to_string tcenv normalized in
                 FStar_Util.JsonStr uu____8911 in
               (QueryOK, uu____8910))
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | NameContainsStr _0 -> true | uu____8946 -> false
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee -> match projectee with | NameContainsStr _0 -> _0
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeContainsLid _0 -> true | uu____8968 -> false
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee -> match projectee with | TypeContainsLid _0 -> _0
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee ->
    match projectee with | { st_negate; st_term;_} -> st_negate
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee -> match projectee with | { st_negate; st_term;_} -> st_term
let (st_cost : search_term' -> Prims.int) =
  fun uu___8_9003 ->
    match uu___8_9003 with
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
    let uu____9137 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____9144 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____9137; sc_fvars = uu____9144 }
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv ->
    fun sc ->
      let uu____9168 = FStar_ST.op_Bang sc.sc_typ in
      match uu____9168 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None ->
          let typ =
            let uu____9196 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____9196 with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____9215, typ), uu____9217) ->
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
      let uu____9267 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____9267 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None ->
          let fv =
            let uu____9311 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____9311 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv ->
    fun sc ->
      let typ_str =
        let uu____9355 = sc_typ tcenv sc in
        FStar_QueryHelper.term_to_string tcenv uu____9355 in
      let uu____9356 =
        let uu____9364 =
          let uu____9370 =
            let uu____9371 =
              let uu____9373 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              uu____9373.FStar_Ident.str in
            FStar_Util.JsonStr uu____9371 in
          ("lid", uu____9370) in
        [uu____9364; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____9356
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidSearch uu____9406 -> true
    | uu____9409 -> false
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | InvalidSearch uu____9419 -> uu____9419
let run_search :
  'Auu____9428 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state, 'Auu____9428)
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
              let uu____9475 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____9475 in
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
              let uu____9534 =
                let uu____9535 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____9535 in
              FStar_Exn.raise uu____9534
            else
              if beg_quote
              then
                (let uu____9541 = strip_quotes term1 in
                 NameContainsStr uu____9541)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____9546 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____9546 with
                 | FStar_Pervasives_Native.None ->
                     let uu____9549 =
                       let uu____9550 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____9550 in
                     FStar_Exn.raise uu____9549
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____9578 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____9578 in
      let results =
        try
          (fun uu___1204_9612 ->
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
                        let uu____9660 = FStar_List.map pprint_one terms in
                        FStar_Util.concat_l " " uu____9660 in
                      let uu____9666 =
                        let uu____9667 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds in
                        InvalidSearch uu____9667 in
                      FStar_Exn.raise uu____9666
                  | uu____9674 -> (QueryOK, (FStar_Util.JsonList js)))) ()
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
          { push_kind = SyntaxCheck; push_code = uu____9805;
            push_line = uu____9806; push_column = uu____9807;
            push_peek_only = false;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____9813 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____9815 -> q)
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
      let uu____9888 = validate_and_run_query st query in
      match uu____9888 with
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
      let uu____9954 = deserialize_interactive_query query_js in
      js_repl_eval st uu____9954
let (js_repl_eval_str :
  repl_state ->
    Prims.string ->
      (Prims.string * (repl_state, Prims.int) FStar_Util.either))
  =
  fun st ->
    fun query_str ->
      let uu____9978 =
        let uu____9988 = parse_interactive_query query_str in
        js_repl_eval st uu____9988 in
      match uu____9978 with
      | (js_response, st_opt) ->
          let uu____10011 = FStar_Util.string_of_json js_response in
          (uu____10011, st_opt)
let (js_repl_init_opts : unit -> unit) =
  fun uu____10024 ->
    let uu____10025 = FStar_Options.parse_cmd_line () in
    match uu____10025 with
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
              | h::uu____10048::uu____10049 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____10058 -> ()))
let rec (go : repl_state -> Prims.int) =
  fun st ->
    let query = read_interactive_query st.repl_stdin in
    let uu____10071 = validate_and_run_query st query in
    match uu____10071 with
    | ((status, response), state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____10124 =
      let uu____10127 = FStar_ST.op_Bang issues in e :: uu____10127 in
    FStar_ST.op_Colon_Equals issues uu____10124 in
  let count_errors uu____10181 =
    let uu____10182 =
      let uu____10185 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____10185 in
    FStar_List.length uu____10182 in
  let report uu____10220 =
    let uu____10221 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____10221 in
  let clear1 uu____10252 = FStar_ST.op_Colon_Equals issues [] in
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
               let uu____10313 = get_json () in
               forward_message printer label uu____10313)
    }
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
let (initial_range : FStar_Range.range) =
  let uu____10327 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  let uu____10330 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  FStar_Range.mk_range "<input>" uu____10327 uu____10330
let (build_initial_repl_state : Prims.string -> repl_state) =
  fun filename ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range in
    let uu____10344 = FStar_Util.open_stdin () in
    {
      repl_line = (Prims.parse_int "1");
      repl_column = (Prims.parse_int "0");
      repl_fname = filename;
      repl_deps_stack = [];
      repl_curmod = FStar_Pervasives_Native.None;
      repl_env = env1;
      repl_stdin = uu____10344;
      repl_names = FStar_Interactive_CompletionTable.empty
    }
let interactive_mode' : 'Auu____10360 . repl_state -> 'Auu____10360 =
  fun init_st ->
    write_hello ();
    (let exit_code =
       let uu____10369 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____10369
       then
         let uu____10373 =
           let uu____10375 = FStar_Options.file_list () in
           FStar_List.hd uu____10375 in
         FStar_SMTEncoding_Solver.with_hints_db uu____10373
           (fun uu____10382 -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let (interactive_mode : Prims.string -> unit) =
  fun filename ->
    install_ide_mode_hooks FStar_JsonHelper.write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____10396 =
       let uu____10398 = FStar_Options.codegen () in
       FStar_Option.isSome uu____10398 in
     if uu____10396
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename in
     let uu____10407 = FStar_Options.trace_error () in
     if uu____10407
     then interactive_mode' init1
     else
       (try
          (fun uu___1352_10413 ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___1351_10416 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1351_10416)))