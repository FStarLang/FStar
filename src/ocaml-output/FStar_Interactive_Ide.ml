open Prims
exception ExitREPL of Prims.int
let uu___is_ExitREPL: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | ExitREPL uu____7 -> true | uu____8 -> false
let __proj__ExitREPL__item__uu___: Prims.exn -> Prims.int =
  fun projectee  -> match projectee with | ExitREPL uu____15 -> uu____15
let push:
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun msg  ->
      let res = FStar_Universal.push_context env msg in
      FStar_Options.push (); res
let pop: FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  -> FStar_Universal.pop_context env msg; FStar_Options.pop ()
type push_kind =
  | SyntaxCheck
  | LaxCheck
  | FullCheck[@@deriving show]
let uu___is_SyntaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____34 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____38 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____42 -> false
let set_check_kind:
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun check_kind  ->
      let uu___91_49 = env in
      let uu____50 =
        FStar_ToSyntax_Env.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___91_49.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___91_49.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___91_49.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___91_49.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___91_49.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___91_49.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___91_49.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___91_49.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___91_49.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___91_49.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___91_49.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___91_49.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___91_49.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___91_49.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___91_49.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___91_49.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___91_49.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___91_49.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___91_49.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___91_49.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___91_49.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___91_49.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___91_49.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___91_49.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___91_49.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___91_49.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___91_49.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___91_49.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___91_49.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___91_49.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___91_49.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____50;
        FStar_TypeChecker_Env.dep_graph =
          (uu___91_49.FStar_TypeChecker_Env.dep_graph)
      }
let with_captured_errors':
  'Auu____54 .
    FStar_TypeChecker_Env.env ->
      (FStar_TypeChecker_Env.env -> 'Auu____54 FStar_Pervasives_Native.option)
        -> 'Auu____54 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun f  ->
      try f env
      with
      | FStar_All.Failure msg ->
          let msg1 =
            Prims.strcat "ASSERTION FAILURE: "
              (Prims.strcat msg
                 (Prims.strcat "\n"
                    (Prims.strcat "F* may be in an inconsistent state.\n"
                       (Prims.strcat
                          "Please file a bug report, ideally with a "
                          "minimized version of the program that triggered the error.")))) in
          ((let uu____90 = FStar_TypeChecker_Env.get_range env in
            FStar_Errors.log_issue uu____90
              (FStar_Errors.Error_IDEAssertionFailure, msg1));
           FStar_Pervasives_Native.None)
      | FStar_Errors.Error (e,msg,r) ->
          (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
           FStar_Pervasives_Native.None)
      | FStar_Errors.Err (e,msg) ->
          ((let uu____110 =
              let uu____119 =
                let uu____126 = FStar_TypeChecker_Env.get_range env in
                (e, msg, uu____126) in
              [uu____119] in
            FStar_TypeChecker_Err.add_errors env uu____110);
           FStar_Pervasives_Native.None)
      | FStar_Errors.Stop  -> FStar_Pervasives_Native.None
let with_captured_errors:
  'Auu____142 .
    FStar_TypeChecker_Env.env ->
      (FStar_TypeChecker_Env.env ->
         'Auu____142 FStar_Pervasives_Native.option)
        -> 'Auu____142 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun f  ->
      let uu____162 = FStar_Options.trace_error () in
      if uu____162 then f env else with_captured_errors' env f
type timed_fname = {
  tf_fname: Prims.string;
  tf_modtime: FStar_Util.time;}[@@deriving show]
let __proj__Mktimed_fname__item__tf_fname: timed_fname -> Prims.string =
  fun projectee  ->
    match projectee with
    | { tf_fname = __fname__tf_fname; tf_modtime = __fname__tf_modtime;_} ->
        __fname__tf_fname
let __proj__Mktimed_fname__item__tf_modtime: timed_fname -> FStar_Util.time =
  fun projectee  ->
    match projectee with
    | { tf_fname = __fname__tf_fname; tf_modtime = __fname__tf_modtime;_} ->
        __fname__tf_modtime
let t0: FStar_Util.time = FStar_Util.now ()
let tf_of_fname: Prims.string -> timed_fname =
  fun fname  ->
    let uu____187 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname in
    { tf_fname = fname; tf_modtime = uu____187 }
let dummy_tf_of_fname: Prims.string -> timed_fname =
  fun fname  -> { tf_fname = fname; tf_modtime = t0 }
let string_of_timed_fname: timed_fname -> Prims.string =
  fun uu____193  ->
    match uu____193 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____197 = FStar_Util.string_of_time modtime in
           FStar_Util.format2 "{ %s; %s }" fname uu____197)
type push_query =
  {
  push_kind: push_kind;
  push_code: Prims.string;
  push_line: Prims.int;
  push_column: Prims.int;
  push_peek_only: Prims.bool;}[@@deriving show]
let __proj__Mkpush_query__item__push_kind: push_query -> push_kind =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_kind
let __proj__Mkpush_query__item__push_code: push_query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_code
let __proj__Mkpush_query__item__push_line: push_query -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_line
let __proj__Mkpush_query__item__push_column: push_query -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_column
let __proj__Mkpush_query__item__push_peek_only: push_query -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} ->
        __fname__push_peek_only
type optmod_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
[@@deriving show]
type repl_task =
  | LDInterleaved of (timed_fname,timed_fname)
  FStar_Pervasives_Native.tuple2
  | LDSingle of timed_fname
  | LDInterfaceOfCurrentFile of timed_fname
  | PushFragment of FStar_Parser_ParseIt.input_frag[@@deriving show]
let uu___is_LDInterleaved: repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | LDInterleaved _0 -> true | uu____288 -> false
let __proj__LDInterleaved__item___0:
  repl_task -> (timed_fname,timed_fname) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LDInterleaved _0 -> _0
let uu___is_LDSingle: repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | LDSingle _0 -> true | uu____312 -> false
let __proj__LDSingle__item___0: repl_task -> timed_fname =
  fun projectee  -> match projectee with | LDSingle _0 -> _0
let uu___is_LDInterfaceOfCurrentFile: repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____324 -> false
let __proj__LDInterfaceOfCurrentFile__item___0: repl_task -> timed_fname =
  fun projectee  -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let uu___is_PushFragment: repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | PushFragment _0 -> true | uu____336 -> false
let __proj__PushFragment__item___0:
  repl_task -> FStar_Parser_ParseIt.input_frag =
  fun projectee  -> match projectee with | PushFragment _0 -> _0
type env_t = FStar_TypeChecker_Env.env[@@deriving show]
type repl_state =
  {
  repl_line: Prims.int;
  repl_column: Prims.int;
  repl_fname: Prims.string;
  repl_deps_stack:
    (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list;
  repl_curmod: optmod_t;
  repl_env: env_t;
  repl_stdin: FStar_Util.stream_reader;
  repl_names: FStar_Interactive_CompletionTable.table;}[@@deriving show]
let __proj__Mkrepl_state__item__repl_line: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_line
let __proj__Mkrepl_state__item__repl_column: repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_column
let __proj__Mkrepl_state__item__repl_fname: repl_state -> Prims.string =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_fname
let __proj__Mkrepl_state__item__repl_deps_stack:
  repl_state ->
    (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_deps_stack
let __proj__Mkrepl_state__item__repl_curmod: repl_state -> optmod_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_curmod
let __proj__Mkrepl_state__item__repl_env: repl_state -> env_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_env
let __proj__Mkrepl_state__item__repl_stdin:
  repl_state -> FStar_Util.stream_reader =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_stdin
let __proj__Mkrepl_state__item__repl_names:
  repl_state -> FStar_Interactive_CompletionTable.table =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_names
type completed_repl_task =
  (repl_task,repl_state) FStar_Pervasives_Native.tuple2[@@deriving show]
type repl_stack_t =
  (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list[@@deriving
                                                                    show]
let repl_stack:
  (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let pop_repl: repl_state -> repl_state =
  fun st  ->
    let uu____572 = FStar_ST.op_Bang repl_stack in
    match uu____572 with
    | [] -> failwith "Too many pops"
    | (uu____614,st')::stack ->
        (pop st.repl_env "#pop";
         FStar_ST.op_Colon_Equals repl_stack stack;
         st')
let push_repl:
  push_kind -> repl_task -> repl_state -> FStar_TypeChecker_Env.env =
  fun push_kind  ->
    fun task  ->
      fun st  ->
        (let uu____670 =
           let uu____677 = FStar_ST.op_Bang repl_stack in (task, st) ::
             uu____677 in
         FStar_ST.op_Colon_Equals repl_stack uu____670);
        (let uu____750 = set_check_kind st.repl_env push_kind in
         push uu____750 "")
let nothing_left_to_pop: repl_state -> Prims.bool =
  fun st  ->
    let uu____754 =
      let uu____755 = FStar_ST.op_Bang repl_stack in
      FStar_List.length uu____755 in
    uu____754 = (FStar_List.length st.repl_deps_stack)
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple3
  | NTOpen of (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
  FStar_Pervasives_Native.tuple2
  | NTInclude of (FStar_Ident.lid,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2
  | NTBinding of FStar_TypeChecker_Env.binding[@@deriving show]
let uu___is_NTAlias: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____845 -> false
let __proj__NTAlias__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | NTAlias _0 -> _0
let uu___is_NTOpen: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____879 -> false
let __proj__NTOpen__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTOpen _0 -> _0
let uu___is_NTInclude: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____907 -> false
let __proj__NTInclude__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTInclude _0 -> _0
let uu___is_NTBinding: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____931 -> false
let __proj__NTBinding__item___0:
  name_tracking_event -> FStar_TypeChecker_Env.binding =
  fun projectee  -> match projectee with | NTBinding _0 -> _0
let query_of_ids:
  FStar_Ident.ident Prims.list -> FStar_Interactive_CompletionTable.query =
  fun ids  -> FStar_List.map FStar_Ident.text_of_id ids
let query_of_lid:
  FStar_Ident.lident -> FStar_Interactive_CompletionTable.query =
  fun lid  ->
    query_of_ids
      (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident])
let update_names_from_event:
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table
  =
  fun cur_mod_str  ->
    fun table  ->
      fun evt  ->
        let is_cur_mod lid = lid.FStar_Ident.str = cur_mod_str in
        match evt with
        | NTAlias (host,id1,included) ->
            if is_cur_mod host
            then
              let uu____965 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                (FStar_Ident.text_of_id id1) [] uu____965
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____974 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_ToSyntax_Env.Open_module) [] uu____974
            else table
        | NTInclude (host,included) ->
            let uu____978 = if is_cur_mod host then [] else query_of_lid host in
            let uu____980 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____978 uu____980
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_TypeChecker_Env.Binding_lid (lid,uu____988) -> [lid]
              | FStar_TypeChecker_Env.Binding_sig (lids,uu____990) -> lids
              | FStar_TypeChecker_Env.Binding_sig_inst
                  (lids,uu____996,uu____997) -> lids
              | uu____1002 -> [] in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     (FStar_Ident.text_of_id lid.FStar_Ident.ident) lid)
              table lids
let commit_name_tracking':
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event Prims.list ->
        FStar_Interactive_CompletionTable.table
  =
  fun cur_mod  ->
    fun names1  ->
      fun name_events  ->
        let cur_mod_str =
          match cur_mod with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some md ->
              let uu____1033 = FStar_Syntax_Syntax.mod_name md in
              uu____1033.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let commit_name_tracking:
  repl_state -> name_tracking_event Prims.list -> repl_state =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events in
      let uu___94_1050 = st in
      {
        repl_line = (uu___94_1050.repl_line);
        repl_column = (uu___94_1050.repl_column);
        repl_fname = (uu___94_1050.repl_fname);
        repl_deps_stack = (uu___94_1050.repl_deps_stack);
        repl_curmod = (uu___94_1050.repl_curmod);
        repl_env = (uu___94_1050.repl_env);
        repl_stdin = (uu___94_1050.repl_stdin);
        repl_names = names1
      }
let fresh_name_tracking_hooks:
  Prims.unit ->
    (name_tracking_event Prims.list FStar_ST.ref,FStar_ToSyntax_Env.dsenv_hooks,
      FStar_TypeChecker_Env.tcenv_hooks) FStar_Pervasives_Native.tuple3
  =
  fun uu____1063  ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____1075 =
        let uu____1078 = FStar_ST.op_Bang events in evt :: uu____1078 in
      FStar_ST.op_Colon_Equals events uu____1075 in
    (events,
      {
        FStar_ToSyntax_Env.ds_push_open_hook =
          (fun dsenv  ->
             fun op  ->
               let uu____1205 =
                 let uu____1206 =
                   let uu____1211 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____1211, op) in
                 NTOpen uu____1206 in
               push_event uu____1205);
        FStar_ToSyntax_Env.ds_push_include_hook =
          (fun dsenv  ->
             fun ns  ->
               let uu____1217 =
                 let uu____1218 =
                   let uu____1223 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____1223, ns) in
                 NTInclude uu____1218 in
               push_event uu____1217);
        FStar_ToSyntax_Env.ds_push_module_abbrev_hook =
          (fun dsenv  ->
             fun x  ->
               fun l  ->
                 let uu____1231 =
                   let uu____1232 =
                     let uu____1239 = FStar_ToSyntax_Env.current_module dsenv in
                     (uu____1239, x, l) in
                   NTAlias uu____1232 in
                 push_event uu____1231)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1244  -> fun s  -> push_event (NTBinding s))
      })
let track_name_changes:
  env_t ->
    (env_t,env_t ->
             (env_t,name_tracking_event Prims.list)
               FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    let set_hooks dshooks tchooks env1 =
      let uu____1283 =
        FStar_Universal.with_tcenv env1
          (fun dsenv  ->
             let uu____1291 = FStar_ToSyntax_Env.set_ds_hooks dsenv dshooks in
             ((), uu____1291)) in
      match uu____1283 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu____1293 =
      let uu____1298 =
        FStar_ToSyntax_Env.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu____1299 = FStar_TypeChecker_Env.tc_hooks env in
      (uu____1298, uu____1299) in
    match uu____1293 with
    | (old_dshooks,old_tchooks) ->
        let uu____1314 = fresh_name_tracking_hooks () in
        (match uu____1314 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____1348 = set_hooks new_dshooks new_tchooks env in
             (uu____1348,
               ((fun env1  ->
                   let uu____1361 = set_hooks old_dshooks old_tchooks env1 in
                   let uu____1362 =
                     let uu____1365 = FStar_ST.op_Bang events in
                     FStar_List.rev uu____1365 in
                   (uu____1361, uu____1362)))))
let string_of_repl_task: repl_task -> Prims.string =
  fun uu___76_1417  ->
    match uu___76_1417 with
    | LDInterleaved (intf,impl) ->
        let uu____1420 = string_of_timed_fname intf in
        let uu____1421 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1420 uu____1421
    | LDSingle intf_or_impl ->
        let uu____1423 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____1423
    | LDInterfaceOfCurrentFile intf ->
        let uu____1425 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1425
    | PushFragment frag ->
        FStar_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
let tc_one:
  FStar_TypeChecker_Env.env ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun intf_opt  ->
      fun modf  ->
        let uu____1440 = FStar_Universal.tc_one_file env intf_opt modf in
        match uu____1440 with | (uu____1449,env1) -> env1
let run_repl_task:
  optmod_t ->
    env_t -> repl_task -> (optmod_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____1478 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname in
            (curmod, uu____1478)
        | LDSingle intf_or_impl ->
            let uu____1480 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname in
            (curmod, uu____1480)
        | LDInterfaceOfCurrentFile intf ->
            let uu____1482 =
              FStar_Universal.load_interface_decls env intf.tf_fname in
            (curmod, uu____1482)
        | PushFragment frag ->
            FStar_Universal.tc_one_fragment curmod env frag
let repl_ld_tasks_of_deps:
  Prims.string Prims.list -> repl_task Prims.list -> repl_task Prims.list =
  fun deps  ->
    fun final_tasks  ->
      let wrap = dummy_tf_of_fname in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____1527 = aux deps' final_tasks1 in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____1527
        | intf_or_impl::deps' ->
            let uu____1534 = aux deps' final_tasks1 in
            (LDSingle (wrap intf_or_impl)) :: uu____1534
        | [] -> final_tasks1 in
      aux deps final_tasks
let deps_and_repl_ld_tasks_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,repl_task Prims.list,FStar_Parser_Dep.deps)
      FStar_Pervasives_Native.tuple3
  =
  fun filename  ->
    let get_mod_name fname = FStar_Parser_Dep.lowercase_module_name fname in
    let our_mod_name = get_mod_name filename in
    let has_our_mod_name f =
      let uu____1569 = get_mod_name f in uu____1569 = our_mod_name in
    let uu____1570 = FStar_Dependencies.find_deps_if_needed [filename] in
    match uu____1570 with
    | (deps,dep_graph1) ->
        let uu____1593 = FStar_List.partition has_our_mod_name deps in
        (match uu____1593 with
         | (same_name,real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____1630 =
                       let uu____1631 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu____1631 in
                     if uu____1630
                     then
                       let uu____1632 =
                         let uu____1637 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.Fatal_MissingInterface, uu____1637) in
                       FStar_Errors.raise_err uu____1632
                     else ());
                    (let uu____1640 =
                       let uu____1641 =
                         FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu____1641 in
                     if uu____1640
                     then
                       let uu____1642 =
                         let uu____1647 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____1647) in
                       FStar_Errors.raise_err uu____1642
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____1650 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu____1656 =
                       let uu____1661 =
                         FStar_Util.format2 message our_mod_name mods_str in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____1661) in
                     FStar_Errors.raise_err uu____1656);
                    []) in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
             (real_deps, tasks, dep_graph1))
let update_task_timestamps: repl_task -> repl_task =
  fun uu___77_1671  ->
    match uu___77_1671 with
    | LDInterleaved (intf,impl) ->
        let uu____1674 =
          let uu____1679 = tf_of_fname intf.tf_fname in
          let uu____1680 = tf_of_fname impl.tf_fname in
          (uu____1679, uu____1680) in
        LDInterleaved uu____1674
    | LDSingle intf_or_impl ->
        let uu____1682 = tf_of_fname intf_or_impl.tf_fname in
        LDSingle uu____1682
    | LDInterfaceOfCurrentFile intf ->
        let uu____1684 = tf_of_fname intf.tf_fname in
        LDInterfaceOfCurrentFile uu____1684
    | PushFragment frag -> PushFragment frag
let run_repl_transaction:
  repl_state ->
    push_kind ->
      Prims.bool ->
        repl_task -> (Prims.bool,repl_state) FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun push_kind  ->
      fun must_rollback  ->
        fun task  ->
          let env = push_repl push_kind task st in
          let uu____1703 = track_name_changes env in
          match uu____1703 with
          | (env1,finish_name_tracking) ->
              let check_success uu____1741 =
                (let uu____1744 = FStar_Errors.get_err_count () in
                 uu____1744 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback) in
              let uu____1745 =
                let uu____1752 =
                  with_captured_errors env1
                    (fun env2  ->
                       let uu____1766 =
                         run_repl_task st.repl_curmod env2 task in
                       FStar_All.pipe_left
                         (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
                         uu____1766) in
                match uu____1752 with
                | FStar_Pervasives_Native.Some (curmod,env2) when
                    check_success () -> (curmod, env2, true)
                | uu____1797 -> ((st.repl_curmod), env1, false) in
              (match uu____1745 with
               | (curmod,env2,success) ->
                   let uu____1811 = finish_name_tracking env2 in
                   (match uu____1811 with
                    | (env',name_events) ->
                        let st1 =
                          let uu___95_1829 = st in
                          {
                            repl_line = (uu___95_1829.repl_line);
                            repl_column = (uu___95_1829.repl_column);
                            repl_fname = (uu___95_1829.repl_fname);
                            repl_deps_stack = (uu___95_1829.repl_deps_stack);
                            repl_curmod = curmod;
                            repl_env = env2;
                            repl_stdin = (uu___95_1829.repl_stdin);
                            repl_names = (uu___95_1829.repl_names)
                          } in
                        let st2 =
                          if success
                          then commit_name_tracking st1 name_events
                          else pop_repl st1 in
                        (success, st2)))
let run_repl_ld_transactions:
  repl_state ->
    repl_task Prims.list -> (repl_state,repl_state) FStar_Util.either
  =
  fun st  ->
    fun tasks  ->
      let debug1 verb task =
        let uu____1853 = FStar_Options.debug_any () in
        if uu____1853
        then
          let uu____1854 = string_of_repl_task task in
          FStar_Util.print2 "%s %s" verb uu____1854
        else () in
      let rec revert_many st1 uu___78_1868 =
        match uu___78_1868 with
        | [] -> st1
        | (task,_st')::entries ->
            ((let uu____1893 = Obj.magic () in ());
             debug1 "Reverting" task;
             (let uu____1895 = pop_repl st1 in revert_many uu____1895 entries)) in
      let rec aux st1 tasks1 previous =
        match (tasks1, previous) with
        | ([],[]) -> FStar_Util.Inl st1
        | (task::tasks2,[]) ->
            (debug1 "Loading" task;
             (let uu____1940 = FStar_Options.restore_cmd_line_options false in
              FStar_All.pipe_right uu____1940 FStar_Pervasives.ignore);
             (let timestamped_task = update_task_timestamps task in
              let push_kind =
                let uu____1943 = FStar_Options.lax () in
                if uu____1943 then LaxCheck else FullCheck in
              let uu____1945 =
                run_repl_transaction st1 push_kind false timestamped_task in
              match uu____1945 with
              | (success,st2) ->
                  if success
                  then
                    let uu____1960 =
                      let uu___96_1961 = st2 in
                      let uu____1962 = FStar_ST.op_Bang repl_stack in
                      {
                        repl_line = (uu___96_1961.repl_line);
                        repl_column = (uu___96_1961.repl_column);
                        repl_fname = (uu___96_1961.repl_fname);
                        repl_deps_stack = uu____1962;
                        repl_curmod = (uu___96_1961.repl_curmod);
                        repl_env = (uu___96_1961.repl_env);
                        repl_stdin = (uu___96_1961.repl_stdin);
                        repl_names = (uu___96_1961.repl_names)
                      } in
                    aux uu____1960 tasks2 []
                  else FStar_Util.Inr st2))
        | (task::tasks2,prev::previous1) when
            let uu____2013 = update_task_timestamps task in
            (FStar_Pervasives_Native.fst prev) = uu____2013 ->
            (debug1 "Skipping" task; aux st1 tasks2 previous1)
        | (tasks2,previous1) ->
            let uu____2025 = revert_many st1 previous1 in
            aux uu____2025 tasks2 [] in
      aux st tasks (FStar_List.rev st.repl_deps_stack)
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___79_2032  ->
    match uu___79_2032 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2036 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2036
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2038 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2041 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____2058 -> true
    | uu____2063 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____2078 -> uu____2078
let js_fail: 'Auu____2086 . Prims.string -> FStar_Util.json -> 'Auu____2086 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___80_2097  ->
    match uu___80_2097 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___81_2102  ->
    match uu___81_2102 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____2108 .
    (FStar_Util.json -> 'Auu____2108) ->
      FStar_Util.json -> 'Auu____2108 Prims.list
  =
  fun k  ->
    fun uu___82_2121  ->
      match uu___82_2121 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___83_2138  ->
    match uu___83_2138 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____2162 = js_str s in
    match uu____2162 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____2163 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____2167 = js_str s in
    match uu____2167 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____2168 -> js_fail "reduction rule" s
type completion_context =
  | CKCode
  | CKOption of Prims.bool
  | CKModuleOrNamespace of (Prims.bool,Prims.bool)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_CKCode: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____2184 -> false
let uu___is_CKOption: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____2189 -> false
let __proj__CKOption__item___0: completion_context -> Prims.bool =
  fun projectee  -> match projectee with | CKOption _0 -> _0
let uu___is_CKModuleOrNamespace: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____2205 -> false
let __proj__CKModuleOrNamespace__item___0:
  completion_context ->
    (Prims.bool,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0
let js_optional_completion_context:
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2233 = js_str k1 in
        (match uu____2233 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____2234 ->
             js_fail
               "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
type lookup_context =
  | LKSymbolOnly
  | LKModule
  | LKOption
  | LKCode[@@deriving show]
let uu___is_LKSymbolOnly: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKSymbolOnly  -> true | uu____2238 -> false
let uu___is_LKModule: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____2242 -> false
let uu___is_LKOption: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____2246 -> false
let uu___is_LKCode: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____2250 -> false
let js_optional_lookup_context:
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2259 = js_str k1 in
        (match uu____2259 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____2260 ->
             js_fail
               "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
type position =
  (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3[@@deriving
                                                                    show]
type query' =
  | Exit
  | DescribeProtocol
  | DescribeRepl
  | Segment of Prims.string
  | Pop
  | Push of push_query
  | VfsAdd of (Prims.string FStar_Pervasives_Native.option,Prims.string)
  FStar_Pervasives_Native.tuple2
  | AutoComplete of (Prims.string,completion_context)
  FStar_Pervasives_Native.tuple2
  | Lookup of
  (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
  Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  | Compute of
  (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                  FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | Search of Prims.string
  | GenericError of Prims.string
  | ProtocolViolation of Prims.string[@@deriving show]
and query = {
  qq: query';
  qid: Prims.string;}[@@deriving show]
let uu___is_Exit: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2344 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____2348 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____2352 -> false
let uu___is_Segment: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____2357 -> false
let __proj__Segment__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Segment _0 -> _0
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____2368 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____2373 -> false
let __proj__Push__item___0: query' -> push_query =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_VfsAdd: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____2391 -> false
let __proj__VfsAdd__item___0:
  query' ->
    (Prims.string FStar_Pervasives_Native.option,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | VfsAdd _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____2425 -> false
let __proj__AutoComplete__item___0:
  query' -> (Prims.string,completion_context) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2461 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
      Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2517 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2553 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_GenericError: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____2565 -> false
let __proj__GenericError__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | GenericError _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2577 -> false
let __proj__ProtocolViolation__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0
let __proj__Mkquery__item__qq: query -> query' =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qq
let __proj__Mkquery__item__qid: query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qid
let query_needs_current_module: query' -> Prims.bool =
  fun uu___84_2597  ->
    match uu___84_2597 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____2598 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____2599; push_code = uu____2600;
          push_line = uu____2601; push_column = uu____2602;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____2603 -> false
    | GenericError uu____2610 -> false
    | ProtocolViolation uu____2611 -> false
    | Push uu____2612 -> true
    | AutoComplete uu____2613 -> true
    | Lookup uu____2618 -> true
    | Compute uu____2631 -> true
    | Search uu____2640 -> true
let interactive_protocol_vernum: Prims.int = Prims.parse_int "2"
let interactive_protocol_features: Prims.string Prims.list =
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
  "vfs-add"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____2649 -> true
    | uu____2650 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2657 -> uu____2657
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol[@@deriving show]
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2661 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2665 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2669 -> false
let try_assoc:
  'Auu____2674 'Auu____2675 .
    'Auu____2675 ->
      ('Auu____2675,'Auu____2674) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2674 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2698 =
        FStar_Util.try_find
          (fun uu____2712  ->
             match uu____2712 with | (k,uu____2718) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2698
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2732 =
          let uu____2733 =
            let uu____2734 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2734 in
          ProtocolViolation uu____2733 in
        { qq = uu____2732; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2760 = try_assoc key a in
      match uu____2760 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2764 =
            let uu____2765 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2765 in
          FStar_Exn.raise uu____2764 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2780 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2780 js_str in
    try
      let query =
        let uu____2789 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2789 js_str in
      let args =
        let uu____2797 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____2797 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____2814 = try_assoc k args in
        match uu____2814 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____2822 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "segment" ->
            let uu____2823 =
              let uu____2824 = arg "code" in
              FStar_All.pipe_right uu____2824 js_str in
            Segment uu____2823
        | "peek" ->
            let uu____2825 =
              let uu____2826 =
                let uu____2827 = arg "kind" in
                FStar_All.pipe_right uu____2827 js_pushkind in
              let uu____2828 =
                let uu____2829 = arg "code" in
                FStar_All.pipe_right uu____2829 js_str in
              let uu____2830 =
                let uu____2831 = arg "line" in
                FStar_All.pipe_right uu____2831 js_int in
              let uu____2832 =
                let uu____2833 = arg "column" in
                FStar_All.pipe_right uu____2833 js_int in
              {
                push_kind = uu____2826;
                push_code = uu____2828;
                push_line = uu____2830;
                push_column = uu____2832;
                push_peek_only = (query = "peek")
              } in
            Push uu____2825
        | "push" ->
            let uu____2834 =
              let uu____2835 =
                let uu____2836 = arg "kind" in
                FStar_All.pipe_right uu____2836 js_pushkind in
              let uu____2837 =
                let uu____2838 = arg "code" in
                FStar_All.pipe_right uu____2838 js_str in
              let uu____2839 =
                let uu____2840 = arg "line" in
                FStar_All.pipe_right uu____2840 js_int in
              let uu____2841 =
                let uu____2842 = arg "column" in
                FStar_All.pipe_right uu____2842 js_int in
              {
                push_kind = uu____2835;
                push_code = uu____2837;
                push_line = uu____2839;
                push_column = uu____2841;
                push_peek_only = (query = "peek")
              } in
            Push uu____2834
        | "autocomplete" ->
            let uu____2843 =
              let uu____2848 =
                let uu____2849 = arg "partial-symbol" in
                FStar_All.pipe_right uu____2849 js_str in
              let uu____2850 =
                let uu____2851 = try_arg "context" in
                FStar_All.pipe_right uu____2851
                  js_optional_completion_context in
              (uu____2848, uu____2850) in
            AutoComplete uu____2843
        | "lookup" ->
            let uu____2856 =
              let uu____2869 =
                let uu____2870 = arg "symbol" in
                FStar_All.pipe_right uu____2870 js_str in
              let uu____2871 =
                let uu____2872 = try_arg "context" in
                FStar_All.pipe_right uu____2872 js_optional_lookup_context in
              let uu____2877 =
                let uu____2886 =
                  let uu____2895 = try_arg "location" in
                  FStar_All.pipe_right uu____2895
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____2886
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____2953 =
                          let uu____2954 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____2954 js_str in
                        let uu____2955 =
                          let uu____2956 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____2956 js_int in
                        let uu____2957 =
                          let uu____2958 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____2958 js_int in
                        (uu____2953, uu____2955, uu____2957))) in
              let uu____2959 =
                let uu____2962 = arg "requested-info" in
                FStar_All.pipe_right uu____2962 (js_list js_str) in
              (uu____2869, uu____2871, uu____2877, uu____2959) in
            Lookup uu____2856
        | "compute" ->
            let uu____2975 =
              let uu____2984 =
                let uu____2985 = arg "term" in
                FStar_All.pipe_right uu____2985 js_str in
              let uu____2986 =
                let uu____2991 = try_arg "rules" in
                FStar_All.pipe_right uu____2991
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____2984, uu____2986) in
            Compute uu____2975
        | "search" ->
            let uu____3006 =
              let uu____3007 = arg "terms" in
              FStar_All.pipe_right uu____3007 js_str in
            Search uu____3006
        | "vfs-add" ->
            let uu____3008 =
              let uu____3015 =
                let uu____3018 = try_arg "filename" in
                FStar_All.pipe_right uu____3018
                  (FStar_Util.map_option js_str) in
              let uu____3025 =
                let uu____3026 = arg "contents" in
                FStar_All.pipe_right uu____3026 js_str in
              (uu____3015, uu____3025) in
            VfsAdd uu____3008
        | uu____3029 ->
            let uu____3030 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____3030 in
      { qq = uu____2822; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____3043 = FStar_Util.read_line stream in
      match uu____3043 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise (ExitREPL (Prims.parse_int "0"))
      | FStar_Pervasives_Native.Some line ->
          let uu____3047 = FStar_Util.json_of_string line in
          (match uu____3047 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let json_of_opt:
  'Auu____3060 .
    ('Auu____3060 -> FStar_Util.json) ->
      'Auu____3060 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____3078 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____3078
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____3084 =
      let uu____3087 =
        let uu____3088 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____3088 in
      let uu____3089 =
        let uu____3092 =
          let uu____3093 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____3093 in
        [uu____3092] in
      uu____3087 :: uu____3089 in
    FStar_Util.JsonList uu____3084
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____3103 =
          let uu____3110 =
            let uu____3117 =
              let uu____3122 = json_of_pos b in ("beg", uu____3122) in
            let uu____3123 =
              let uu____3130 =
                let uu____3135 = json_of_pos e in ("end", uu____3135) in
              [uu____3130] in
            uu____3117 :: uu____3123 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____3110 in
        FStar_Util.JsonAssoc uu____3103
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____3155 = FStar_Range.file_of_use_range r in
    let uu____3156 = FStar_Range.start_of_use_range r in
    let uu____3157 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____3155 uu____3156 uu____3157
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____3161 = FStar_Range.file_of_range r in
    let uu____3162 = FStar_Range.start_of_range r in
    let uu____3163 = FStar_Range.end_of_range r in
    json_of_range_fields uu____3161 uu____3162 uu____3163
let json_of_issue_level: FStar_Errors.issue_level -> FStar_Util.json =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
let json_of_issue: FStar_Errors.issue -> FStar_Util.json =
  fun issue  ->
    let uu____3170 =
      let uu____3177 =
        let uu____3184 =
          let uu____3191 =
            let uu____3196 =
              let uu____3197 =
                let uu____3200 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____3206 = json_of_use_range r in [uu____3206] in
                let uu____3207 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____3213 = FStar_Range.def_range r in
                      let uu____3214 = FStar_Range.use_range r in
                      uu____3213 <> uu____3214 ->
                      let uu____3215 = json_of_def_range r in [uu____3215]
                  | uu____3216 -> [] in
                FStar_List.append uu____3200 uu____3207 in
              FStar_Util.JsonList uu____3197 in
            ("ranges", uu____3196) in
          [uu____3191] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____3184 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____3177 in
    FStar_Util.JsonAssoc uu____3170
type symbol_lookup_result =
  {
  slr_name: Prims.string;
  slr_def_range: FStar_Range.range FStar_Pervasives_Native.option;
  slr_typ: Prims.string FStar_Pervasives_Native.option;
  slr_doc: Prims.string FStar_Pervasives_Native.option;
  slr_def: Prims.string FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mksymbol_lookup_result__item__slr_name:
  symbol_lookup_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_name
let __proj__Mksymbol_lookup_result__item__slr_def_range:
  symbol_lookup_result -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_def_range
let __proj__Mksymbol_lookup_result__item__slr_typ:
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_typ
let __proj__Mksymbol_lookup_result__item__slr_doc:
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_doc
let __proj__Mksymbol_lookup_result__item__slr_def:
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_def
let alist_of_symbol_lookup_result:
  symbol_lookup_result ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun lr  ->
    let uu____3368 =
      let uu____3375 =
        let uu____3380 = json_of_opt json_of_def_range lr.slr_def_range in
        ("defined-at", uu____3380) in
      let uu____3381 =
        let uu____3388 =
          let uu____3393 =
            json_of_opt (fun _0_65  -> FStar_Util.JsonStr _0_65) lr.slr_typ in
          ("type", uu____3393) in
        let uu____3394 =
          let uu____3401 =
            let uu____3406 =
              json_of_opt (fun _0_66  -> FStar_Util.JsonStr _0_66) lr.slr_doc in
            ("documentation", uu____3406) in
          let uu____3407 =
            let uu____3414 =
              let uu____3419 =
                json_of_opt (fun _0_67  -> FStar_Util.JsonStr _0_67)
                  lr.slr_def in
              ("definition", uu____3419) in
            [uu____3414] in
          uu____3401 :: uu____3407 in
        uu____3388 :: uu____3394 in
      uu____3375 :: uu____3381 in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____3368
let alist_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3452 =
      FStar_List.map (fun _0_68  -> FStar_Util.JsonStr _0_68)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_69  -> FStar_Util.JsonList _0_69) uu____3452 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet
  | OptReset
  | OptReadOnly[@@deriving show]
let uu___is_OptSet: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____3472 -> false
let uu___is_OptReset: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____3476 -> false
let uu___is_OptReadOnly: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____3480 -> false
let string_of_option_permission_level:
  fstar_option_permission_level -> Prims.string =
  fun uu___85_3483  ->
    match uu___85_3483 with
    | OptSet  -> ""
    | OptReset  -> "requires #reset-options"
    | OptReadOnly  -> "read-only"
type fstar_option =
  {
  opt_name: Prims.string;
  opt_sig: Prims.string;
  opt_value: FStar_Options.option_val;
  opt_default: FStar_Options.option_val;
  opt_type: FStar_Options.opt_type;
  opt_snippets: Prims.string Prims.list;
  opt_documentation: Prims.string FStar_Pervasives_Native.option;
  opt_permission_level: fstar_option_permission_level;}[@@deriving show]
let __proj__Mkfstar_option__item__opt_name: fstar_option -> Prims.string =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_name
let __proj__Mkfstar_option__item__opt_sig: fstar_option -> Prims.string =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_sig
let __proj__Mkfstar_option__item__opt_value:
  fstar_option -> FStar_Options.option_val =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_value
let __proj__Mkfstar_option__item__opt_default:
  fstar_option -> FStar_Options.option_val =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_default
let __proj__Mkfstar_option__item__opt_type:
  fstar_option -> FStar_Options.opt_type =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_type
let __proj__Mkfstar_option__item__opt_snippets:
  fstar_option -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_snippets
let __proj__Mkfstar_option__item__opt_documentation:
  fstar_option -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_documentation
let __proj__Mkfstar_option__item__opt_permission_level:
  fstar_option -> fstar_option_permission_level =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_permission_level
let rec kind_of_fstar_option_type: FStar_Options.opt_type -> Prims.string =
  fun uu___86_3650  ->
    match uu___86_3650 with
    | FStar_Options.Const uu____3651 -> "flag"
    | FStar_Options.IntStr uu____3652 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____3653 -> "path"
    | FStar_Options.SimpleStr uu____3654 -> "string"
    | FStar_Options.EnumStr uu____3655 -> "enum"
    | FStar_Options.OpenEnumStr uu____3658 -> "open enum"
    | FStar_Options.PostProcessed (uu____3665,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____3673,typ) ->
        kind_of_fstar_option_type typ
let rec snippets_of_fstar_option:
  Prims.string -> FStar_Options.opt_type -> Prims.string Prims.list =
  fun name  ->
    fun typ  ->
      let mk_field field_name =
        Prims.strcat "${" (Prims.strcat field_name "}") in
      let mk_snippet name1 argstring =
        Prims.strcat "--"
          (Prims.strcat name1
             (if argstring <> "" then Prims.strcat " " argstring else "")) in
      let rec arg_snippets_of_type typ1 =
        match typ1 with
        | FStar_Options.Const uu____3707 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____3720,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____3728,elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____3734 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____3734
let rec json_of_fstar_option_value:
  FStar_Options.option_val -> FStar_Util.json =
  fun uu___87_3739  ->
    match uu___87_3739 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____3747 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____3747
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let alist_of_fstar_option:
  fstar_option ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun opt  ->
    let uu____3759 =
      let uu____3766 =
        let uu____3773 =
          let uu____3778 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____3778) in
        let uu____3779 =
          let uu____3786 =
            let uu____3791 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____3791) in
          let uu____3792 =
            let uu____3799 =
              let uu____3804 =
                json_of_opt (fun _0_70  -> FStar_Util.JsonStr _0_70)
                  opt.opt_documentation in
              ("documentation", uu____3804) in
            let uu____3805 =
              let uu____3812 =
                let uu____3817 =
                  let uu____3818 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____3818 in
                ("type", uu____3817) in
              [uu____3812;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____3799 :: uu____3805 in
          uu____3786 :: uu____3792 in
        uu____3773 :: uu____3779 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3766 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3759
let json_of_fstar_option: fstar_option -> FStar_Util.json =
  fun opt  ->
    let uu____3854 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____3854
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____3865 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____3865);
    FStar_Util.print_raw "\n"
let write_response:
  Prims.string -> query_status -> FStar_Util.json -> Prims.unit =
  fun qid  ->
    fun status  ->
      fun response  ->
        let qid1 = FStar_Util.JsonStr qid in
        let status1 =
          match status with
          | QueryOK  -> FStar_Util.JsonStr "success"
          | QueryNOK  -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol  -> FStar_Util.JsonStr "protocol-violation" in
        write_json
          (FStar_Util.JsonAssoc
             [("kind", (FStar_Util.JsonStr "response"));
             ("query-id", qid1);
             ("status", status1);
             ("response", response)])
let write_message: Prims.string -> FStar_Util.json -> Prims.unit =
  fun level  ->
    fun contents  ->
      write_json
        (FStar_Util.JsonAssoc
           [("kind", (FStar_Util.JsonStr "message"));
           ("level", (FStar_Util.JsonStr level));
           ("contents", contents)])
let write_hello: Prims.unit -> Prims.unit =
  fun uu____3921  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____3924 =
        FStar_List.map (fun _0_71  -> FStar_Util.JsonStr _0_71)
          interactive_protocol_features in
      FStar_Util.JsonList uu____3924 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: alist_of_protocol_info))
let sig_of_fstar_option:
  Prims.string -> FStar_Options.opt_type -> Prims.string =
  fun name  ->
    fun typ  ->
      let flag = Prims.strcat "--" name in
      let uu____3938 = FStar_Options.desc_of_opt_type typ in
      match uu____3938 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.strcat flag (Prims.strcat " " arg_sig)
let fstar_options_list_cache: fstar_option Prims.list =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____3947 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____3976  ->
            match uu____3976 with
            | (_shortname,name,typ,doc1) ->
                let uu____3991 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____3991
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____4003 = sig_of_fstar_option name typ in
                        let uu____4004 = snippets_of_fstar_option name typ in
                        let uu____4007 =
                          let uu____4008 = FStar_Options.settable name in
                          if uu____4008
                          then OptSet
                          else
                            (let uu____4010 = FStar_Options.resettable name in
                             if uu____4010 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____4003;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____4004;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____4007
                        })))) in
  FStar_All.pipe_right uu____3947
    (FStar_List.sortWith
       (fun o1  ->
          fun o2  ->
            FStar_String.compare (FStar_String.lowercase o1.opt_name)
              (FStar_String.lowercase o2.opt_name)))
let fstar_options_map_cache: fstar_option FStar_Util.smap =
  let cache = FStar_Util.smap_create (Prims.parse_int "50") in
  FStar_List.iter (fun opt  -> FStar_Util.smap_add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache
let update_option: fstar_option -> fstar_option =
  fun opt  ->
    let uu___101_4034 = opt in
    let uu____4035 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___101_4034.opt_name);
      opt_sig = (uu___101_4034.opt_sig);
      opt_value = uu____4035;
      opt_default = (uu___101_4034.opt_default);
      opt_type = (uu___101_4034.opt_type);
      opt_snippets = (uu___101_4034.opt_snippets);
      opt_documentation = (uu___101_4034.opt_documentation);
      opt_permission_level = (uu___101_4034.opt_permission_level)
    }
let current_fstar_options:
  (fstar_option -> Prims.bool) -> fstar_option Prims.list =
  fun filter1  ->
    let uu____4046 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____4046
let trim_option_name:
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun opt_name  ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____4061 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____4061)
    else ("", opt_name)
let json_of_repl_state: repl_state -> FStar_Util.json =
  fun st  ->
    let filenames uu____4075 =
      match uu____4075 with
      | (task,uu____4083) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | PushFragment uu____4090 -> []) in
    let uu____4091 =
      let uu____4098 =
        let uu____4103 =
          let uu____4104 =
            let uu____4107 =
              FStar_List.concatMap filenames st.repl_deps_stack in
            FStar_List.map (fun _0_72  -> FStar_Util.JsonStr _0_72)
              uu____4107 in
          FStar_Util.JsonList uu____4104 in
        ("loaded-dependencies", uu____4103) in
      let uu____4114 =
        let uu____4121 =
          let uu____4126 =
            let uu____4127 =
              let uu____4130 =
                current_fstar_options (fun uu____4135  -> true) in
              FStar_List.map json_of_fstar_option uu____4130 in
            FStar_Util.JsonList uu____4127 in
          ("options", uu____4126) in
        [uu____4121] in
      uu____4098 :: uu____4114 in
    FStar_Util.JsonAssoc uu____4091
let with_printed_effect_args:
  'Auu____4150 . (Prims.unit -> 'Auu____4150) -> 'Auu____4150 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____4162  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____4171  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____4176  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____4180 'Auu____4181 .
    'Auu____4181 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4180,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____4209 'Auu____4210 .
    'Auu____4210 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4210,'Auu____4209) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____4237 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4237) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4254 =
      let uu____4259 = json_of_repl_state st in (QueryOK, uu____4259) in
    (uu____4254, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____4272 'Auu____4273 .
    'Auu____4273 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4273,'Auu____4272) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error:
  'Auu____4306 'Auu____4307 .
    'Auu____4307 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4307,'Auu____4306) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let collect_errors: Prims.unit -> FStar_Errors.issue Prims.list =
  fun uu____4340  ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment:
  'Auu____4348 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4348) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun code  ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
          FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
        } in
      let collect_decls uu____4375 =
        let uu____4376 = FStar_Parser_Driver.parse_fragment frag in
        match uu____4376 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____4382,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____4388,decls,uu____4390)) -> decls in
      let uu____4395 =
        with_captured_errors st.repl_env
          (fun uu____4404  ->
             let uu____4405 = collect_decls () in
             FStar_All.pipe_left
               (fun _0_73  -> FStar_Pervasives_Native.Some _0_73) uu____4405) in
      match uu____4395 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____4433 = collect_errors () in
            FStar_All.pipe_right uu____4433 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____4457 =
              let uu____4464 =
                let uu____4469 =
                  json_of_def_range (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu____4469) in
              [uu____4464] in
            FStar_Util.JsonAssoc uu____4457 in
          let js_decls =
            let uu____4479 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left (fun _0_74  -> FStar_Util.JsonList _0_74)
              uu____4479 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add:
  'Auu____4504 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____4504) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop:
  'Auu____4545 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4545) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4562 = nothing_left_to_pop st in
    if uu____4562
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let st' = pop_repl st in
       ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))
let load_deps:
  repl_state ->
    ((repl_state,Prims.string Prims.list) FStar_Pervasives_Native.tuple2,
      repl_state) FStar_Util.either
  =
  fun st  ->
    let uu____4606 =
      with_captured_errors st.repl_env
        (fun _env  ->
           let uu____4632 = deps_and_repl_ld_tasks_of_our_file st.repl_fname in
           FStar_All.pipe_left
             (fun _0_75  -> FStar_Pervasives_Native.Some _0_75) uu____4632) in
    match uu____4606 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___102_4723 = st in
          let uu____4724 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1 in
          {
            repl_line = (uu___102_4723.repl_line);
            repl_column = (uu___102_4723.repl_column);
            repl_fname = (uu___102_4723.repl_fname);
            repl_deps_stack = (uu___102_4723.repl_deps_stack);
            repl_curmod = (uu___102_4723.repl_curmod);
            repl_env = uu____4724;
            repl_stdin = (uu___102_4723.repl_stdin);
            repl_names = (uu___102_4723.repl_names)
          } in
        let uu____4725 = run_repl_ld_transactions st1 tasks in
        (match uu____4725 with
         | FStar_Util.Inr st2 -> FStar_Util.Inr st2
         | FStar_Util.Inl st2 -> FStar_Util.Inl (st2, deps))
let rephrase_dependency_error: FStar_Errors.issue -> FStar_Errors.issue =
  fun issue  ->
    let uu___103_4759 = issue in
    let uu____4760 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____4760;
      FStar_Errors.issue_level = (uu___103_4759.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___103_4759.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___103_4759.FStar_Errors.issue_number)
    }
let run_push_without_deps:
  'Auu____4764 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4764) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___104_4792 = st1 in
        {
          repl_line = (uu___104_4792.repl_line);
          repl_column = (uu___104_4792.repl_column);
          repl_fname = (uu___104_4792.repl_fname);
          repl_deps_stack = (uu___104_4792.repl_deps_stack);
          repl_curmod = (uu___104_4792.repl_curmod);
          repl_env =
            (let uu___105_4794 = st1.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___105_4794.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___105_4794.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___105_4794.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___105_4794.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___105_4794.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___105_4794.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___105_4794.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___105_4794.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___105_4794.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___105_4794.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___105_4794.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___105_4794.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___105_4794.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___105_4794.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___105_4794.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___105_4794.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___105_4794.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___105_4794.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___105_4794.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___105_4794.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___105_4794.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.tc_term =
                 (uu___105_4794.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___105_4794.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___105_4794.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___105_4794.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___105_4794.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___105_4794.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___105_4794.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___105_4794.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___105_4794.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___105_4794.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___105_4794.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.dep_graph =
                 (uu___105_4794.FStar_TypeChecker_Env.dep_graph)
             });
          repl_stdin = (uu___104_4792.repl_stdin);
          repl_names = (uu___104_4792.repl_names)
        } in
      let uu____4795 = query in
      match uu____4795 with
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
            let uu____4816 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag) in
            match uu____4816 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____4839 =
                    let uu____4842 = collect_errors () in
                    FStar_All.pipe_right uu____4842
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____4839 in
                let st4 =
                  if success
                  then
                    let uu___106_4850 = st3 in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___106_4850.repl_fname);
                      repl_deps_stack = (uu___106_4850.repl_deps_stack);
                      repl_curmod = (uu___106_4850.repl_curmod);
                      repl_env = (uu___106_4850.repl_env);
                      repl_stdin = (uu___106_4850.repl_stdin);
                      repl_names = (uu___106_4850.repl_names)
                    }
                  else st3 in
                ((status, json_errors), (FStar_Util.Inl st4))))
let capitalize: Prims.string -> Prims.string =
  fun str  ->
    if str = ""
    then str
    else
      (let first =
         FStar_String.substring str (Prims.parse_int "0")
           (Prims.parse_int "1") in
       let uu____4865 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1")) in
       Prims.strcat (FStar_String.uppercase first) uu____4865)
let add_module_completions:
  Prims.string ->
    Prims.string Prims.list ->
      FStar_Interactive_CompletionTable.table ->
        FStar_Interactive_CompletionTable.table
  =
  fun this_fname  ->
    fun deps  ->
      fun table  ->
        let mods = FStar_Parser_Dep.build_inclusion_candidates_list () in
        let loaded_mods_set =
          let uu____4889 = FStar_Util.psmap_empty () in
          let uu____4892 =
            let uu____4895 = FStar_Options.prims () in uu____4895 :: deps in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____4905 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____4905 true) uu____4889
            uu____4892 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____4921  ->
               match uu____4921 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____4933 = capitalize modname in
                        FStar_Util.split uu____4933 "." in
                      let uu____4934 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____4934 mod_path ns_query)) table
          (FStar_List.rev mods)
let run_push_with_deps:
  'Auu____4942 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4942) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      (let uu____4964 = FStar_Options.debug_any () in
       if uu____4964
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____4967 = load_deps st in
       match uu____4967 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____5000 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____5000 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____5031 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____5031 FStar_Pervasives.ignore);
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names in
             run_push_without_deps
               (let uu___107_5034 = st1 in
                {
                  repl_line = (uu___107_5034.repl_line);
                  repl_column = (uu___107_5034.repl_column);
                  repl_fname = (uu___107_5034.repl_fname);
                  repl_deps_stack = (uu___107_5034.repl_deps_stack);
                  repl_curmod = (uu___107_5034.repl_curmod);
                  repl_env = (uu___107_5034.repl_env);
                  repl_stdin = (uu___107_5034.repl_stdin);
                  repl_names = names1
                }) query)))
let run_push:
  'Auu____5038 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5038) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let uu____5059 = nothing_left_to_pop st in
      if uu____5059
      then run_push_with_deps st query
      else run_push_without_deps st query
let run_symbol_lookup:
  repl_state ->
    Prims.string ->
      (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
                          FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let tcenv = st.repl_env in
          let info_of_lid_str lid_str =
            let lid =
              let uu____5137 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".") in
              FStar_Ident.lid_of_ids uu____5137 in
            let lid1 =
              let uu____5141 =
                FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____5141 in
            let uu____5146 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
            FStar_All.pipe_right uu____5146
              (FStar_Util.map_option
                 (fun uu____5201  ->
                    match uu____5201 with
                    | ((uu____5220,typ),r) -> ((FStar_Util.Inr lid1), typ, r))) in
          let docs_of_lid lid =
            let uu____5237 =
              FStar_ToSyntax_Env.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid in
            FStar_All.pipe_right uu____5237
              (FStar_Util.map_option FStar_Pervasives_Native.fst) in
          let def_of_lid lid =
            let uu____5266 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
            FStar_Util.bind_opt uu____5266
              (fun uu___88_5310  ->
                 match uu___88_5310 with
                 | (FStar_Util.Inr (se,uu____5332),uu____5333) ->
                     let uu____5362 = sigelt_to_string se in
                     FStar_Pervasives_Native.Some uu____5362
                 | uu____5363 -> FStar_Pervasives_Native.None) in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____5415  ->
                 match uu____5415 with
                 | (file,row,col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____5462 -> info_at_pos_opt
            | FStar_Pervasives_Native.None  ->
                if symbol = ""
                then FStar_Pervasives_Native.None
                else info_of_lid_str symbol in
          let response =
            match info_opt with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                let name =
                  match name_or_lid with
                  | FStar_Util.Inl name -> name
                  | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
                let typ_str =
                  if FStar_List.mem "type" requested_info
                  then
                    let uu____5590 = term_to_string tcenv typ in
                    FStar_Pervasives_Native.Some uu____5590
                  else FStar_Pervasives_Native.None in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____5598 -> FStar_Pervasives_Native.None in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____5609 -> FStar_Pervasives_Native.None in
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
                let uu____5621 =
                  let uu____5632 = alist_of_symbol_lookup_result result in
                  ("symbol", uu____5632) in
                FStar_Pervasives_Native.Some uu____5621 in
          match response with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some info -> FStar_Util.Inr info
let run_option_lookup:
  Prims.string ->
    (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
                    FStar_Pervasives_Native.tuple2)
      FStar_Util.either
  =
  fun opt_name  ->
    let uu____5737 = trim_option_name opt_name in
    match uu____5737 with
    | (uu____5756,trimmed_name) ->
        let uu____5758 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____5758 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.strcat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____5786 =
               let uu____5797 =
                 let uu____5804 = update_option opt in
                 alist_of_fstar_option uu____5804 in
               ("option", uu____5797) in
             FStar_Util.Inr uu____5786)
let run_module_lookup:
  repl_state ->
    Prims.string ->
      (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                    FStar_Pervasives_Native.tuple2 Prims.list)
                      FStar_Pervasives_Native.tuple2)
        FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      let query = FStar_Util.split symbol "." in
      let uu____5844 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query in
      match uu____5844 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____5872 =
            let uu____5883 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____5883) in
          FStar_Util.Inr uu____5872
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____5907 =
            let uu____5918 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____5918) in
          FStar_Util.Inr uu____5907
let run_code_lookup:
  repl_state ->
    Prims.string ->
      (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
                          FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____5987 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____5987 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____6047 ->
              let uu____6058 = run_module_lookup st symbol in
              (match uu____6058 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
let run_lookup':
  repl_state ->
    Prims.string ->
      lookup_context ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list)
                            FStar_Pervasives_Native.tuple2)
              FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            match context with
            | LKSymbolOnly  ->
                run_symbol_lookup st symbol pos_opt requested_info
            | LKModule  -> run_module_lookup st symbol
            | LKOption  -> run_option_lookup symbol
            | LKCode  -> run_code_lookup st symbol pos_opt requested_info
let run_lookup:
  'Auu____6208 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6208) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____6261 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____6261 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let code_autocomplete_mod_filter:
  'Auu____6345 .
    ('Auu____6345,FStar_Interactive_CompletionTable.mod_symbol)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____6345,FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu___89_6359  ->
    match uu___89_6359 with
    | (uu____6364,FStar_Interactive_CompletionTable.Namespace uu____6365) ->
        FStar_Pervasives_Native.None
    | (uu____6370,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____6371;
         FStar_Interactive_CompletionTable.mod_path = uu____6372;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____6379 =
          let uu____6384 =
            let uu____6385 =
              let uu___108_6386 = md in
              let uu____6387 =
                let uu____6388 =
                  FStar_Interactive_CompletionTable.mod_name md in
                Prims.strcat uu____6388 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____6387;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___108_6386.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___108_6386.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____6385 in
          (pth, uu____6384) in
        FStar_Pervasives_Native.Some uu____6379
let run_code_autocomplete:
  'Auu____6396 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6396) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
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
let run_module_autocomplete:
  'Auu____6444 'Auu____6445 'Auu____6446 .
    repl_state ->
      Prims.string ->
        'Auu____6446 ->
          'Auu____6445 ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____6444) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun modules1  ->
        fun namespaces  ->
          let needle = FStar_Util.split search_term "." in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.repl_names needle
              (fun _0_76  -> FStar_Pervasives_Native.Some _0_76) in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
let candidates_of_fstar_option:
  Prims.int ->
    Prims.bool ->
      fstar_option ->
        FStar_Interactive_CompletionTable.completion_result Prims.list
  =
  fun match_len  ->
    fun is_reset  ->
      fun opt  ->
        let uu____6507 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only") in
        match uu____6507 with
        | (may_set,explanation) ->
            let opt_type = kind_of_fstar_option_type opt.opt_type in
            let annot =
              if may_set
              then opt_type
              else
                Prims.strcat "("
                  (Prims.strcat explanation
                     (Prims.strcat " " (Prims.strcat opt_type ")"))) in
            FStar_All.pipe_right opt.opt_snippets
              (FStar_List.map
                 (fun snippet  ->
                    {
                      FStar_Interactive_CompletionTable.completion_match_length
                        = match_len;
                      FStar_Interactive_CompletionTable.completion_candidate
                        = snippet;
                      FStar_Interactive_CompletionTable.completion_annotation
                        = annot
                    }))
let run_option_autocomplete:
  'Auu____6534 'Auu____6535 .
    'Auu____6535 ->
      Prims.string ->
        Prims.bool ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            ('Auu____6535,'Auu____6534) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____6560 = trim_option_name search_term in
        match uu____6560 with
        | ("--",trimmed_name) ->
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
        | (uu____6611,uu____6612) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete:
  'Auu____6625 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____6625) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun context  ->
        match context with
        | CKCode  -> run_code_autocomplete st search_term
        | CKOption is_reset ->
            run_option_autocomplete st search_term is_reset
        | CKModuleOrNamespace (modules1,namespaces) ->
            run_module_autocomplete st search_term modules1 namespaces
let run_and_rewind:
  'Auu____6657 'Auu____6658 .
    repl_state ->
      (repl_state -> 'Auu____6658) ->
        ('Auu____6658,(repl_state,'Auu____6657) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun task  ->
      let env' = push st.repl_env "#compute" in
      let results =
        try
          let uu____6697 = task st in
          FStar_All.pipe_left (fun _0_77  -> FStar_Util.Inl _0_77) uu____6697
        with | e -> FStar_Util.Inr e in
      pop env' "#compute";
      (match results with
       | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st))
       | FStar_Util.Inr e -> FStar_Exn.raise e)
let run_with_parsed_and_tc_term:
  'Auu____6741 'Auu____6742 'Auu____6743 .
    repl_state ->
      Prims.string ->
        'Auu____6743 ->
          'Auu____6742 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term ->
                 (query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2)
              ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6741) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun term  ->
      fun line  ->
        fun column  ->
          fun continuation  ->
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
                    ((uu____6827,{ FStar_Syntax_Syntax.lbname = uu____6828;
                                   FStar_Syntax_Syntax.lbunivs = univs1;
                                   FStar_Syntax_Syntax.lbtyp = uu____6830;
                                   FStar_Syntax_Syntax.lbeff = uu____6831;
                                   FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____6833);
                  FStar_Syntax_Syntax.sigrng = uu____6834;
                  FStar_Syntax_Syntax.sigquals = uu____6835;
                  FStar_Syntax_Syntax.sigmeta = uu____6836;
                  FStar_Syntax_Syntax.sigattrs = uu____6837;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____6876 -> FStar_Pervasives_Native.None in
            let parse1 frag =
              let uu____6895 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu____6895 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____6901) ->
                  FStar_Pervasives_Native.Some decls
              | uu____6926 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu____6940 =
                let uu____6945 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu____6945 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu____6940 in
            let typecheck tcenv decls =
              let uu____6963 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu____6963 with | (ses,uu____6977,uu____6978) -> ses in
            run_and_rewind st
              (fun st1  ->
                 let tcenv = st1.repl_env in
                 let frag = dummy_let_fragment term in
                 match st1.repl_curmod with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                 | uu____7001 ->
                     let uu____7002 = parse1 frag in
                     (match uu____7002 with
                      | FStar_Pervasives_Native.None  ->
                          (QueryNOK,
                            (FStar_Util.JsonStr "Could not parse this term"))
                      | FStar_Pervasives_Native.Some decls ->
                          let aux uu____7025 =
                            let decls1 = desugar tcenv decls in
                            let ses = typecheck tcenv decls1 in
                            match find_let_body ses with
                            | FStar_Pervasives_Native.None  ->
                                (QueryNOK,
                                  (FStar_Util.JsonStr
                                     "Typechecking yielded an unexpected term"))
                            | FStar_Pervasives_Native.Some (univs1,def) ->
                                let uu____7060 =
                                  FStar_Syntax_Subst.open_univ_vars univs1
                                    def in
                                (match uu____7060 with
                                 | (univs2,def1) ->
                                     let tcenv1 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         tcenv univs2 in
                                     continuation tcenv1 def1) in
                          let uu____7072 = FStar_Options.trace_error () in
                          if uu____7072
                          then aux ()
                          else
                            (try aux ()
                             with
                             | e ->
                                 let uu____7097 =
                                   let uu____7098 =
                                     FStar_Errors.issue_of_exn e in
                                   match uu____7098 with
                                   | FStar_Pervasives_Native.Some issue ->
                                       let uu____7102 =
                                         FStar_Errors.format_issue issue in
                                       FStar_Util.JsonStr uu____7102
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Exn.raise e in
                                 (QueryNOK, uu____7097))))
let run_compute:
  'Auu____7107 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____7107) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules1 -> rules1
             | FStar_Pervasives_Native.None  ->
                 [FStar_TypeChecker_Normalize.Beta;
                 FStar_TypeChecker_Normalize.Iota;
                 FStar_TypeChecker_Normalize.Zeta;
                 FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant])
            [FStar_TypeChecker_Normalize.Inlining;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.Primops] in
        let normalize_term1 tcenv rules2 t =
          FStar_TypeChecker_Normalize.normalize rules2 tcenv t in
        run_with_parsed_and_tc_term st term (Prims.parse_int "0")
          (Prims.parse_int "0")
          (fun tcenv  ->
             fun def  ->
               let normalized = normalize_term1 tcenv rules1 def in
               let uu____7170 =
                 let uu____7171 = term_to_string tcenv normalized in
                 FStar_Util.JsonStr uu____7171 in
               (QueryOK, uu____7170))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid[@@deriving show]
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}[@@deriving show]
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____7192 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____7204 -> false
let __proj__TypeContainsLid__item___0: search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0
let __proj__Mksearch_term__item__st_negate: search_term -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_negate
let __proj__Mksearch_term__item__st_term: search_term -> search_term' =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_term
let st_cost: search_term' -> Prims.int =
  fun uu___90_7224  ->
    match uu___90_7224 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> Prims.parse_int "1"
type search_candidate =
  {
  sc_lid: FStar_Ident.lid;
  sc_typ:
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref;}[@@deriving show]
let __proj__Mksearch_candidate__item__sc_lid:
  search_candidate -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_lid
let __proj__Mksearch_candidate__item__sc_typ:
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_typ
let __proj__Mksearch_candidate__item__sc_fvars:
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_fvars
let sc_of_lid: FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____7428 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____7435 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____7428; sc_fvars = uu____7435 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____7498 = FStar_ST.op_Bang sc.sc_typ in
      match uu____7498 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____7528 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____7528 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7549,typ),uu____7551) ->
                typ in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
let sc_fvars:
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____7598 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____7598 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____7642 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____7642 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let json_of_search_result:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____7680 = sc_typ tcenv sc in term_to_string tcenv uu____7680 in
      let uu____7681 =
        let uu____7688 =
          let uu____7693 =
            let uu____7694 =
              let uu____7695 =
                FStar_ToSyntax_Env.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              uu____7695.FStar_Ident.str in
            FStar_Util.JsonStr uu____7694 in
          ("lid", uu____7693) in
        [uu____7688; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____7681
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____7714 -> true
    | uu____7715 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____7722 -> uu____7722
let run_search:
  'Auu____7726 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____7726) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_str  ->
      let tcenv = st.repl_env in
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set () in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____7761 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____7761 in
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
              let uu____7785 =
                let uu____7786 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____7786 in
              FStar_Exn.raise uu____7785
            else
              if beg_quote
              then
                (let uu____7788 = strip_quotes term1 in
                 NameContainsStr uu____7788)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____7791 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____7791 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____7794 =
                       let uu____7795 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____7795 in
                     FStar_Exn.raise uu____7794
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____7811 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.strcat (if term.st_negate then "-" else "") uu____7811 in
      let results =
        try
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
          let js = FStar_List.map (json_of_search_result tcenv) sorted1 in
          match results with
          | [] ->
              let kwds =
                let uu____7874 = FStar_List.map pprint_one terms in
                FStar_Util.concat_l " " uu____7874 in
              let uu____7877 =
                let uu____7878 =
                  FStar_Util.format1 "No results found for query [%s]" kwds in
                InvalidSearch uu____7878 in
              FStar_Exn.raise uu____7877
          | uu____7883 -> (QueryOK, (FStar_Util.JsonList js))
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s)) in
      (results, (FStar_Util.Inl st))
let run_query:
  repl_state ->
    query' ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun q  ->
      match q with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | GenericError message -> run_generic_error st message
      | ProtocolViolation query -> run_protocol_violation st query
      | Segment c -> run_segment st c
      | VfsAdd (fname,contents) -> run_vfs_add st fname contents
      | Push pquery -> run_push st pquery
      | Pop  -> run_pop st
      | AutoComplete (search_term,context) ->
          run_autocomplete st search_term context
      | Lookup (symbol,context,pos_opt,rq_info) ->
          run_lookup st symbol context pos_opt rq_info
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
let validate_query: repl_state -> query -> query =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push
          { push_kind = SyntaxCheck ; push_code = uu____7973;
            push_line = uu____7974; push_column = uu____7975;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____7976 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____7977 -> q)
let rec go: repl_state -> Prims.int =
  fun st  ->
    let rec loop st1 =
      let query =
        let uu____7986 = read_interactive_query st1.repl_stdin in
        validate_query st1 uu____7986 in
      let uu____7987 = run_query st1 query.qq in
      match uu____7987 with
      | ((status,response),state_opt) ->
          (write_response query.qid status response;
           (match state_opt with
            | FStar_Util.Inl st' -> loop st'
            | FStar_Util.Inr exitcode -> FStar_Exn.raise (ExitREPL exitcode))) in
    let uu____8018 = FStar_Options.trace_error () in
    if uu____8018 then loop st else (try loop st with | ExitREPL n1 -> n1)
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____8037 =
      let uu____8040 = FStar_ST.op_Bang issues in e :: uu____8040 in
    FStar_ST.op_Colon_Equals issues uu____8037 in
  let count_errors uu____8136 =
    let uu____8137 =
      let uu____8140 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____8140 in
    FStar_List.length uu____8137 in
  let report1 uu____8195 =
    let uu____8196 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8196 in
  let clear1 uu____8247 = FStar_ST.op_Colon_Equals issues [] in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report1;
    FStar_Errors.eh_clear = clear1
  }
let interactive_printer: FStar_Util.printer =
  {
    FStar_Util.printer_prinfo =
      (fun s  -> write_message "info" (FStar_Util.JsonStr s));
    FStar_Util.printer_prwarning =
      (fun s  -> write_message "warning" (FStar_Util.JsonStr s));
    FStar_Util.printer_prerror =
      (fun s  -> write_message "error" (FStar_Util.JsonStr s));
    FStar_Util.printer_prgeneric =
      (fun label1  ->
         fun get_string  ->
           fun get_json  ->
             let uu____8315 = get_json () in write_message label1 uu____8315)
  }
let initial_range: FStar_Range.range =
  let uu____8316 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  let uu____8317 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  FStar_Range.mk_range "<input>" uu____8316 uu____8317
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
     let env1 = FStar_TypeChecker_Env.set_range env initial_range in
     let init_st =
       let uu____8325 = FStar_Util.open_stdin () in
       {
         repl_line = (Prims.parse_int "1");
         repl_column = (Prims.parse_int "0");
         repl_fname = filename;
         repl_deps_stack = [];
         repl_curmod = FStar_Pervasives_Native.None;
         repl_env = env1;
         repl_stdin = uu____8325;
         repl_names = FStar_Interactive_CompletionTable.empty
       } in
     let exit_code =
       let uu____8331 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____8331
       then
         let uu____8332 =
           let uu____8333 = FStar_Options.file_list () in
           FStar_List.hd uu____8333 in
         FStar_SMTEncoding_Solver.with_hints_db uu____8332
           (fun uu____8337  -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    (let uu____8344 =
       let uu____8345 = FStar_Options.codegen () in
       FStar_Option.isSome uu____8345 in
     if uu____8344
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let uu____8349 = FStar_Options.trace_error () in
     if uu____8349
     then interactive_mode' filename
     else
       (try
          FStar_Errors.set_handler interactive_error_handler;
          interactive_mode' filename
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))