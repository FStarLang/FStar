open Prims
exception ExitREPL of Prims.int
let uu___is_ExitREPL: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | ExitREPL uu____8 -> true | uu____9 -> false
let __proj__ExitREPL__item__uu___: Prims.exn -> Prims.int =
  fun projectee  -> match projectee with | ExitREPL uu____17 -> uu____17
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
    match projectee with | SyntaxCheck  -> true | uu____41 -> false
let uu___is_LaxCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____46 -> false
let uu___is_FullCheck: push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____51 -> false
let set_check_kind:
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun check_kind  ->
      let uu___252_60 = env in
      let uu____61 =
        FStar_ToSyntax_Env.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___252_60.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___252_60.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___252_60.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___252_60.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___252_60.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___252_60.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___252_60.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___252_60.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___252_60.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___252_60.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___252_60.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___252_60.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___252_60.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___252_60.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___252_60.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___252_60.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___252_60.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___252_60.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___252_60.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___252_60.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___252_60.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___252_60.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___252_60.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___252_60.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___252_60.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___252_60.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___252_60.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___252_60.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___252_60.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___252_60.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___252_60.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____61
      }
let with_captured_errors':
  'Auu____68 .
    FStar_TypeChecker_Env.env ->
      (FStar_TypeChecker_Env.env -> 'Auu____68 FStar_Pervasives_Native.option)
        -> 'Auu____68 FStar_Pervasives_Native.option
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
          ((let uu____105 =
              let uu____112 =
                let uu____117 = FStar_TypeChecker_Env.get_range env in
                (msg1, uu____117) in
              [uu____112] in
            FStar_TypeChecker_Err.add_errors env uu____105);
           FStar_Util.print_error msg1;
           FStar_Pervasives_Native.None)
      | FStar_Errors.Error (msg,r) ->
          (FStar_TypeChecker_Err.add_errors env [(msg, r)];
           FStar_Pervasives_Native.None)
      | FStar_Errors.Err msg ->
          ((let uu____140 =
              let uu____147 =
                let uu____152 = FStar_TypeChecker_Env.get_range env in
                (msg, uu____152) in
              [uu____147] in
            FStar_TypeChecker_Err.add_errors env uu____140);
           FStar_Pervasives_Native.None)
let with_captured_errors:
  'Auu____167 .
    FStar_TypeChecker_Env.env ->
      (FStar_TypeChecker_Env.env ->
         'Auu____167 FStar_Pervasives_Native.option)
        -> 'Auu____167 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun f  ->
      let uu____187 = FStar_Options.trace_error () in
      if uu____187 then f env else with_captured_errors' env f
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
    let uu____215 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname in
    { tf_fname = fname; tf_modtime = uu____215 }
let dummy_tf_of_fname: Prims.string -> timed_fname =
  fun fname  -> { tf_fname = fname; tf_modtime = t0 }
let string_of_timed_fname: timed_fname -> Prims.string =
  fun uu____223  ->
    match uu____223 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____227 = FStar_Util.string_of_time modtime in
           FStar_Util.format2 "{ %s; %s }" fname uu____227)
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
    match projectee with | LDInterleaved _0 -> true | uu____324 -> false
let __proj__LDInterleaved__item___0:
  repl_task -> (timed_fname,timed_fname) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LDInterleaved _0 -> _0
let uu___is_LDSingle: repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | LDSingle _0 -> true | uu____350 -> false
let __proj__LDSingle__item___0: repl_task -> timed_fname =
  fun projectee  -> match projectee with | LDSingle _0 -> _0
let uu___is_LDInterfaceOfCurrentFile: repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____364 -> false
let __proj__LDInterfaceOfCurrentFile__item___0: repl_task -> timed_fname =
  fun projectee  -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let uu___is_PushFragment: repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | PushFragment _0 -> true | uu____378 -> false
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
    let uu____620 = FStar_ST.op_Bang repl_stack in
    match uu____620 with
    | [] -> failwith "Too many pops"
    | (uu____689,st')::stack ->
        (pop st.repl_env "#pop";
         FStar_ST.op_Colon_Equals repl_stack stack;
         st')
let push_repl:
  push_kind -> repl_task -> repl_state -> FStar_TypeChecker_Env.env =
  fun push_kind  ->
    fun task  ->
      fun st  ->
        (let uu____775 =
           let uu____782 = FStar_ST.op_Bang repl_stack in (task, st) ::
             uu____782 in
         FStar_ST.op_Colon_Equals repl_stack uu____775);
        (let uu____909 = set_check_kind st.repl_env push_kind in
         push uu____909 "")
let nothing_left_to_pop: repl_state -> Prims.bool =
  fun st  ->
    let uu____914 =
      let uu____915 = FStar_ST.op_Bang repl_stack in
      FStar_List.length uu____915 in
    uu____914 = (FStar_List.length st.repl_deps_stack)
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
    match projectee with | NTAlias _0 -> true | uu____1033 -> false
let __proj__NTAlias__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | NTAlias _0 -> _0
let uu___is_NTOpen: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____1069 -> false
let __proj__NTOpen__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTOpen _0 -> _0
let uu___is_NTInclude: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____1099 -> false
let __proj__NTInclude__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTInclude _0 -> _0
let uu___is_NTBinding: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____1125 -> false
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
        | NTAlias (host,id,included) ->
            if is_cur_mod host
            then
              let uu____1165 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                (FStar_Ident.text_of_id id) [] uu____1165
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____1174 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_ToSyntax_Env.Open_module) [] uu____1174
            else table
        | NTInclude (host,included) ->
            let uu____1178 =
              if is_cur_mod host then [] else query_of_lid host in
            let uu____1180 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____1178 uu____1180
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_TypeChecker_Env.Binding_lid (lid,uu____1188) -> [lid]
              | FStar_TypeChecker_Env.Binding_sig (lids,uu____1190) -> lids
              | FStar_TypeChecker_Env.Binding_sig_inst
                  (lids,uu____1196,uu____1197) -> lids
              | uu____1202 -> [] in
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
              let uu____1236 = FStar_Syntax_Syntax.mod_name md in
              uu____1236.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let commit_name_tracking:
  repl_state -> name_tracking_event Prims.list -> repl_state =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events in
      let uu___255_1255 = st in
      {
        repl_line = (uu___255_1255.repl_line);
        repl_column = (uu___255_1255.repl_column);
        repl_fname = (uu___255_1255.repl_fname);
        repl_deps_stack = (uu___255_1255.repl_deps_stack);
        repl_curmod = (uu___255_1255.repl_curmod);
        repl_env = (uu___255_1255.repl_env);
        repl_stdin = (uu___255_1255.repl_stdin);
        repl_names = names1
      }
let fresh_name_tracking_hooks:
  Prims.unit ->
    (name_tracking_event Prims.list FStar_ST.ref,FStar_ToSyntax_Env.dsenv_hooks,
      FStar_TypeChecker_Env.tcenv_hooks) FStar_Pervasives_Native.tuple3
  =
  fun uu____1269  ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____1281 =
        let uu____1284 = FStar_ST.op_Bang events in evt :: uu____1284 in
      FStar_ST.op_Colon_Equals events uu____1281 in
    (events,
      {
        FStar_ToSyntax_Env.ds_push_open_hook =
          (fun dsenv  ->
             fun op  ->
               let uu____1441 =
                 let uu____1442 =
                   let uu____1447 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____1447, op) in
                 NTOpen uu____1442 in
               push_event uu____1441);
        FStar_ToSyntax_Env.ds_push_include_hook =
          (fun dsenv  ->
             fun ns  ->
               let uu____1453 =
                 let uu____1454 =
                   let uu____1459 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____1459, ns) in
                 NTInclude uu____1454 in
               push_event uu____1453);
        FStar_ToSyntax_Env.ds_push_module_abbrev_hook =
          (fun dsenv  ->
             fun x  ->
               fun l  ->
                 let uu____1467 =
                   let uu____1468 =
                     let uu____1475 = FStar_ToSyntax_Env.current_module dsenv in
                     (uu____1475, x, l) in
                   NTAlias uu____1468 in
                 push_event uu____1467)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1480  -> fun s  -> push_event (NTBinding s))
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
      let uu____1520 =
        FStar_Universal.with_tcenv env1
          (fun dsenv  ->
             let uu____1528 = FStar_ToSyntax_Env.set_ds_hooks dsenv dshooks in
             ((), uu____1528)) in
      match uu____1520 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu____1530 =
      let uu____1535 =
        FStar_ToSyntax_Env.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu____1536 = FStar_TypeChecker_Env.tc_hooks env in
      (uu____1535, uu____1536) in
    match uu____1530 with
    | (old_dshooks,old_tchooks) ->
        let uu____1551 = fresh_name_tracking_hooks () in
        (match uu____1551 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____1585 = set_hooks new_dshooks new_tchooks env in
             (uu____1585,
               ((fun env1  ->
                   let uu____1598 = set_hooks old_dshooks old_tchooks env1 in
                   let uu____1599 =
                     let uu____1602 = FStar_ST.op_Bang events in
                     FStar_List.rev uu____1602 in
                   (uu____1598, uu____1599)))))
let string_of_repl_task: repl_task -> Prims.string =
  fun uu___237_1674  ->
    match uu___237_1674 with
    | LDInterleaved (intf,impl) ->
        let uu____1677 = string_of_timed_fname intf in
        let uu____1678 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1677 uu____1678
    | LDSingle intf_or_impl ->
        let uu____1680 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____1680
    | LDInterfaceOfCurrentFile intf ->
        let uu____1682 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1682
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
        let uu____1700 = FStar_Universal.tc_one_file env intf_opt modf in
        match uu____1700 with | (uu____1709,env1) -> env1
let run_repl_task:
  optmod_t ->
    env_t -> repl_task -> (optmod_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____1741 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname in
            (curmod, uu____1741)
        | LDSingle intf_or_impl ->
            let uu____1743 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname in
            (curmod, uu____1743)
        | LDInterfaceOfCurrentFile intf ->
            let uu____1745 =
              FStar_Universal.load_interface_decls env intf.tf_fname in
            (curmod, uu____1745)
        | PushFragment frag ->
            FStar_Universal.tc_one_fragment curmod env (frag, false)
let repl_ld_tasks_of_deps:
  Prims.string Prims.list -> repl_task Prims.list -> repl_task Prims.list =
  fun deps  ->
    fun final_tasks  ->
      let wrap = dummy_tf_of_fname in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____1792 = aux deps' final_tasks1 in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____1792
        | intf_or_impl::deps' ->
            let uu____1799 = aux deps' final_tasks1 in
            (LDSingle (wrap intf_or_impl)) :: uu____1799
        | [] -> final_tasks1 in
      aux deps final_tasks
let deps_and_repl_ld_tasks_of_our_file:
  Prims.string ->
    (Prims.string Prims.list,repl_task Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun filename  ->
    let get_mod_name fname = FStar_Parser_Dep.lowercase_module_name fname in
    let our_mod_name = get_mod_name filename in
    let has_our_mod_name f =
      let uu____1823 = get_mod_name f in uu____1823 = our_mod_name in
    let prims_fname = FStar_Options.prims () in
    let deps =
      let uu____1828 =
        FStar_Dependencies.find_deps_if_needed
          FStar_Parser_Dep.VerifyFigureItOut [filename] in
      prims_fname :: uu____1828 in
    let uu____1831 = FStar_List.partition has_our_mod_name deps in
    match uu____1831 with
    | (same_name,real_deps) ->
        let intf_tasks =
          match same_name with
          | intf::impl::[] ->
              ((let uu____1866 =
                  let uu____1867 = FStar_Parser_Dep.is_interface intf in
                  Prims.op_Negation uu____1867 in
                if uu____1866
                then
                  let uu____1868 =
                    let uu____1869 =
                      FStar_Util.format1 "Expecting an interface, got %s"
                        intf in
                    FStar_Errors.Err uu____1869 in
                  FStar_Exn.raise uu____1868
                else ());
               (let uu____1872 =
                  let uu____1873 = FStar_Parser_Dep.is_implementation impl in
                  Prims.op_Negation uu____1873 in
                if uu____1872
                then
                  let uu____1874 =
                    let uu____1875 =
                      FStar_Util.format1
                        "Expecting an implementation, got %s" impl in
                    FStar_Errors.Err uu____1875 in
                  FStar_Exn.raise uu____1874
                else ());
               [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
          | impl::[] -> []
          | uu____1878 ->
              let mods_str = FStar_String.concat " " same_name in
              let message = "Too many or too few files matching %s: %s" in
              ((let uu____1884 =
                  let uu____1885 =
                    FStar_Util.format2 message our_mod_name mods_str in
                  FStar_Errors.Err uu____1885 in
                FStar_Exn.raise uu____1884);
               []) in
        let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
        (real_deps, tasks)
let update_task_timestamps: repl_task -> repl_task =
  fun uu___238_1896  ->
    match uu___238_1896 with
    | LDInterleaved (intf,impl) ->
        let uu____1899 =
          let uu____1904 = tf_of_fname intf.tf_fname in
          let uu____1905 = tf_of_fname impl.tf_fname in
          (uu____1904, uu____1905) in
        LDInterleaved uu____1899
    | LDSingle intf_or_impl ->
        let uu____1907 = tf_of_fname intf_or_impl.tf_fname in
        LDSingle uu____1907
    | LDInterfaceOfCurrentFile intf ->
        let uu____1909 = tf_of_fname intf.tf_fname in
        LDInterfaceOfCurrentFile uu____1909
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
          let uu____1932 = track_name_changes env in
          match uu____1932 with
          | (env1,finish_name_tracking) ->
              let check_success uu____1970 =
                (let uu____1973 = FStar_Errors.get_err_count () in
                 uu____1973 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback) in
              let uu____1974 =
                let uu____1981 =
                  with_captured_errors env1
                    (fun env2  ->
                       let uu____1995 =
                         run_repl_task st.repl_curmod env2 task in
                       FStar_All.pipe_left
                         (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                         uu____1995) in
                match uu____1981 with
                | FStar_Pervasives_Native.Some (curmod,env2) when
                    check_success () -> (curmod, env2, true)
                | uu____2026 -> ((st.repl_curmod), env1, false) in
              (match uu____1974 with
               | (curmod,env2,success) ->
                   let uu____2040 = finish_name_tracking env2 in
                   (match uu____2040 with
                    | (env',name_events) ->
                        let st1 =
                          let uu___256_2058 = st in
                          {
                            repl_line = (uu___256_2058.repl_line);
                            repl_column = (uu___256_2058.repl_column);
                            repl_fname = (uu___256_2058.repl_fname);
                            repl_deps_stack = (uu___256_2058.repl_deps_stack);
                            repl_curmod = curmod;
                            repl_env = env2;
                            repl_stdin = (uu___256_2058.repl_stdin);
                            repl_names = (uu___256_2058.repl_names)
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
        let uu____2084 = FStar_Options.debug_any () in
        if uu____2084
        then
          let uu____2085 = string_of_repl_task task in
          FStar_Util.print2 "%s %s" verb uu____2085
        else () in
      let rec revert_many st1 uu___239_2099 =
        match uu___239_2099 with
        | [] -> st1
        | (task,_st')::entries ->
            ((let uu____2124 = Obj.magic () in ());
             debug1 "Reverting" task;
             (let uu____2126 = pop_repl st1 in revert_many uu____2126 entries)) in
      let rec aux st1 tasks1 previous =
        match (tasks1, previous) with
        | ([],[]) -> FStar_Util.Inl st1
        | (task::tasks2,[]) ->
            (debug1 "Loading" task;
             (let uu____2171 = FStar_Options.restore_cmd_line_options false in
              FStar_All.pipe_right uu____2171 FStar_Pervasives.ignore);
             (let timestamped_task = update_task_timestamps task in
              let push_kind =
                let uu____2174 = FStar_Options.lax () in
                if uu____2174 then LaxCheck else FullCheck in
              let uu____2176 =
                run_repl_transaction st1 push_kind false timestamped_task in
              match uu____2176 with
              | (success,st2) ->
                  if success
                  then
                    let uu____2191 =
                      let uu___257_2192 = st2 in
                      let uu____2193 = FStar_ST.op_Bang repl_stack in
                      {
                        repl_line = (uu___257_2192.repl_line);
                        repl_column = (uu___257_2192.repl_column);
                        repl_fname = (uu___257_2192.repl_fname);
                        repl_deps_stack = uu____2193;
                        repl_curmod = (uu___257_2192.repl_curmod);
                        repl_env = (uu___257_2192.repl_env);
                        repl_stdin = (uu___257_2192.repl_stdin);
                        repl_names = (uu___257_2192.repl_names)
                      } in
                    aux uu____2191 tasks2 []
                  else FStar_Util.Inr st2))
        | (task::tasks2,prev::previous1) when
            let uu____2271 = update_task_timestamps task in
            (FStar_Pervasives_Native.fst prev) = uu____2271 ->
            (debug1 "Skipping" task; aux st1 tasks2 previous1)
        | (tasks2,previous1) ->
            let uu____2283 = revert_many st1 previous1 in
            aux uu____2283 tasks2 [] in
      aux st tasks (FStar_List.rev st.repl_deps_stack)
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___240_2291  ->
    match uu___240_2291 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2295 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2295
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2297 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2300 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____2318 -> true
    | uu____2323 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____2339 -> uu____2339
let js_fail: 'Auu____2350 . Prims.string -> FStar_Util.json -> 'Auu____2350 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___241_2362  ->
    match uu___241_2362 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___242_2368  ->
    match uu___242_2368 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____2377 .
    (FStar_Util.json -> 'Auu____2377) ->
      FStar_Util.json -> 'Auu____2377 Prims.list
  =
  fun k  ->
    fun uu___243_2390  ->
      match uu___243_2390 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___244_2408  ->
    match uu___244_2408 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____2433 = js_str s in
    match uu____2433 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____2434 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____2439 = js_str s in
    match uu____2439 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____2440 -> js_fail "reduction rule" s
type completion_context =
  | CKCode
  | CKOption of Prims.bool
  | CKModuleOrNamespace of (Prims.bool,Prims.bool)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_CKCode: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____2457 -> false
let uu___is_CKOption: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____2463 -> false
let __proj__CKOption__item___0: completion_context -> Prims.bool =
  fun projectee  -> match projectee with | CKOption _0 -> _0
let uu___is_CKModuleOrNamespace: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____2481 -> false
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
        let uu____2511 = js_str k1 in
        (match uu____2511 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____2512 ->
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
    match projectee with | LKSymbolOnly  -> true | uu____2517 -> false
let uu___is_LKModule: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____2522 -> false
let uu___is_LKOption: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____2527 -> false
let uu___is_LKCode: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____2532 -> false
let js_optional_lookup_context:
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2542 = js_str k1 in
        (match uu____2542 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____2543 ->
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
    match projectee with | Exit  -> true | uu____2624 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____2629 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____2634 -> false
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____2639 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____2645 -> false
let __proj__Push__item___0: query' -> push_query =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_VfsAdd: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____2665 -> false
let __proj__VfsAdd__item___0:
  query' ->
    (Prims.string FStar_Pervasives_Native.option,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | VfsAdd _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____2701 -> false
let __proj__AutoComplete__item___0:
  query' -> (Prims.string,completion_context) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2739 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
      Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2797 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2835 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_GenericError: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____2849 -> false
let __proj__GenericError__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | GenericError _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2863 -> false
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
  fun uu___245_2887  ->
    match uu___245_2887 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Pop  -> false
    | Push
        { push_kind = uu____2888; push_code = uu____2889;
          push_line = uu____2890; push_column = uu____2891;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____2892 -> false
    | GenericError uu____2899 -> false
    | ProtocolViolation uu____2900 -> false
    | Push uu____2901 -> true
    | AutoComplete uu____2902 -> true
    | Lookup uu____2907 -> true
    | Compute uu____2920 -> true
    | Search uu____2929 -> true
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
  "vfs-add";
  "lookup";
  "lookup/context";
  "lookup/documentation";
  "lookup/definition";
  "peek";
  "pop";
  "push";
  "search"]
exception InvalidQuery of Prims.string
let uu___is_InvalidQuery: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____2939 -> true
    | uu____2940 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2948 -> uu____2948
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol[@@deriving show]
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2953 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2958 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2963 -> false
let try_assoc:
  'Auu____2972 'Auu____2973 .
    'Auu____2973 ->
      ('Auu____2973,'Auu____2972) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2972 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2996 =
        FStar_Util.try_find
          (fun uu____3010  ->
             match uu____3010 with | (k,uu____3016) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2996
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____3033 =
          let uu____3034 =
            let uu____3035 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____3035 in
          ProtocolViolation uu____3034 in
        { qq = uu____3033; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____3062 = try_assoc key a in
      match uu____3062 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____3066 =
            let uu____3067 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____3067 in
          FStar_Exn.raise uu____3066 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____3082 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____3082 js_str in
    try
      let query =
        let uu____3091 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____3091 js_str in
      let args =
        let uu____3099 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____3099 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____3116 = try_assoc k args in
        match uu____3116 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____3124 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "peek" ->
            let uu____3125 =
              let uu____3126 =
                let uu____3127 = arg "kind" in
                FStar_All.pipe_right uu____3127 js_pushkind in
              let uu____3128 =
                let uu____3129 = arg "code" in
                FStar_All.pipe_right uu____3129 js_str in
              let uu____3130 =
                let uu____3131 = arg "line" in
                FStar_All.pipe_right uu____3131 js_int in
              let uu____3132 =
                let uu____3133 = arg "column" in
                FStar_All.pipe_right uu____3133 js_int in
              {
                push_kind = uu____3126;
                push_code = uu____3128;
                push_line = uu____3130;
                push_column = uu____3132;
                push_peek_only = (query = "peek")
              } in
            Push uu____3125
        | "push" ->
            let uu____3134 =
              let uu____3135 =
                let uu____3136 = arg "kind" in
                FStar_All.pipe_right uu____3136 js_pushkind in
              let uu____3137 =
                let uu____3138 = arg "code" in
                FStar_All.pipe_right uu____3138 js_str in
              let uu____3139 =
                let uu____3140 = arg "line" in
                FStar_All.pipe_right uu____3140 js_int in
              let uu____3141 =
                let uu____3142 = arg "column" in
                FStar_All.pipe_right uu____3142 js_int in
              {
                push_kind = uu____3135;
                push_code = uu____3137;
                push_line = uu____3139;
                push_column = uu____3141;
                push_peek_only = (query = "peek")
              } in
            Push uu____3134
        | "autocomplete" ->
            let uu____3143 =
              let uu____3148 =
                let uu____3149 = arg "partial-symbol" in
                FStar_All.pipe_right uu____3149 js_str in
              let uu____3150 =
                let uu____3151 = try_arg "context" in
                FStar_All.pipe_right uu____3151
                  js_optional_completion_context in
              (uu____3148, uu____3150) in
            AutoComplete uu____3143
        | "lookup" ->
            let uu____3156 =
              let uu____3169 =
                let uu____3170 = arg "symbol" in
                FStar_All.pipe_right uu____3170 js_str in
              let uu____3171 =
                let uu____3172 = try_arg "context" in
                FStar_All.pipe_right uu____3172 js_optional_lookup_context in
              let uu____3177 =
                let uu____3186 =
                  let uu____3195 = try_arg "location" in
                  FStar_All.pipe_right uu____3195
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____3186
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____3253 =
                          let uu____3254 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____3254 js_str in
                        let uu____3255 =
                          let uu____3256 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____3256 js_int in
                        let uu____3257 =
                          let uu____3258 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____3258 js_int in
                        (uu____3253, uu____3255, uu____3257))) in
              let uu____3259 =
                let uu____3262 = arg "requested-info" in
                FStar_All.pipe_right uu____3262 (js_list js_str) in
              (uu____3169, uu____3171, uu____3177, uu____3259) in
            Lookup uu____3156
        | "compute" ->
            let uu____3275 =
              let uu____3284 =
                let uu____3285 = arg "term" in
                FStar_All.pipe_right uu____3285 js_str in
              let uu____3286 =
                let uu____3291 = try_arg "rules" in
                FStar_All.pipe_right uu____3291
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____3284, uu____3286) in
            Compute uu____3275
        | "search" ->
            let uu____3306 =
              let uu____3307 = arg "terms" in
              FStar_All.pipe_right uu____3307 js_str in
            Search uu____3306
        | "vfs-add" ->
            let uu____3308 =
              let uu____3315 =
                let uu____3318 = try_arg "filename" in
                FStar_All.pipe_right uu____3318
                  (FStar_Util.map_option js_str) in
              let uu____3325 =
                let uu____3326 = arg "contents" in
                FStar_All.pipe_right uu____3326 js_str in
              (uu____3315, uu____3325) in
            VfsAdd uu____3308
        | uu____3329 ->
            let uu____3330 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____3330 in
      { qq = uu____3124; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____3344 = FStar_Util.read_line stream in
      match uu____3344 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise (ExitREPL (Prims.parse_int "0"))
      | FStar_Pervasives_Native.Some line ->
          let uu____3348 = FStar_Util.json_of_string line in
          (match uu____3348 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let json_of_opt:
  'Auu____3364 .
    ('Auu____3364 -> FStar_Util.json) ->
      'Auu____3364 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____3382 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____3382
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____3389 =
      let uu____3392 =
        let uu____3393 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____3393 in
      let uu____3394 =
        let uu____3397 =
          let uu____3398 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____3398 in
        [uu____3397] in
      uu____3392 :: uu____3394 in
    FStar_Util.JsonList uu____3389
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____3411 =
          let uu____3418 =
            let uu____3425 =
              let uu____3430 = json_of_pos b in ("beg", uu____3430) in
            let uu____3431 =
              let uu____3438 =
                let uu____3443 = json_of_pos e in ("end", uu____3443) in
              [uu____3438] in
            uu____3425 :: uu____3431 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____3418 in
        FStar_Util.JsonAssoc uu____3411
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____3464 = FStar_Range.file_of_use_range r in
    let uu____3465 = FStar_Range.start_of_use_range r in
    let uu____3466 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____3464 uu____3465 uu____3466
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____3471 = FStar_Range.file_of_range r in
    let uu____3472 = FStar_Range.start_of_range r in
    let uu____3473 = FStar_Range.end_of_range r in
    json_of_range_fields uu____3471 uu____3472 uu____3473
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
    let uu____3482 =
      let uu____3489 =
        let uu____3496 =
          let uu____3503 =
            let uu____3508 =
              let uu____3509 =
                let uu____3512 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____3518 = json_of_use_range r in [uu____3518] in
                let uu____3519 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      r.FStar_Range.def_range <> r.FStar_Range.use_range ->
                      let uu____3525 = json_of_def_range r in [uu____3525]
                  | uu____3526 -> [] in
                FStar_List.append uu____3512 uu____3519 in
              FStar_Util.JsonList uu____3509 in
            ("ranges", uu____3508) in
          [uu____3503] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____3496 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____3489 in
    FStar_Util.JsonAssoc uu____3482
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
    let uu____3684 =
      let uu____3691 =
        let uu____3696 = json_of_opt json_of_def_range lr.slr_def_range in
        ("defined-at", uu____3696) in
      let uu____3697 =
        let uu____3704 =
          let uu____3709 =
            json_of_opt (fun _0_43  -> FStar_Util.JsonStr _0_43) lr.slr_typ in
          ("type", uu____3709) in
        let uu____3710 =
          let uu____3717 =
            let uu____3722 =
              json_of_opt (fun _0_44  -> FStar_Util.JsonStr _0_44) lr.slr_doc in
            ("documentation", uu____3722) in
          let uu____3723 =
            let uu____3730 =
              let uu____3735 =
                json_of_opt (fun _0_45  -> FStar_Util.JsonStr _0_45)
                  lr.slr_def in
              ("definition", uu____3735) in
            [uu____3730] in
          uu____3717 :: uu____3723 in
        uu____3704 :: uu____3710 in
      uu____3691 :: uu____3697 in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____3684
let alist_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3768 =
      FStar_List.map (fun _0_46  -> FStar_Util.JsonStr _0_46)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_47  -> FStar_Util.JsonList _0_47) uu____3768 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet
  | OptReset
  | OptReadOnly[@@deriving show]
let uu___is_OptSet: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____3789 -> false
let uu___is_OptReset: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____3794 -> false
let uu___is_OptReadOnly: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____3799 -> false
let string_of_option_permission_level:
  fstar_option_permission_level -> Prims.string =
  fun uu___246_3803  ->
    match uu___246_3803 with
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
  fun uu___247_3979  ->
    match uu___247_3979 with
    | FStar_Options.Const uu____3980 -> "flag"
    | FStar_Options.IntStr uu____3981 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____3982 -> "path"
    | FStar_Options.SimpleStr uu____3983 -> "string"
    | FStar_Options.EnumStr uu____3984 -> "enum"
    | FStar_Options.OpenEnumStr uu____3987 -> "open enum"
    | FStar_Options.PostProcessed (uu____3994,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____4002,typ) ->
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
        | FStar_Options.Const uu____4038 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____4051,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____4059,elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____4065 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____4065
let rec json_of_fstar_option_value:
  FStar_Options.option_val -> FStar_Util.json =
  fun uu___248_4071  ->
    match uu___248_4071 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____4079 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____4079
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let alist_of_fstar_option:
  fstar_option ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun opt  ->
    let uu____4092 =
      let uu____4099 =
        let uu____4106 =
          let uu____4111 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____4111) in
        let uu____4112 =
          let uu____4119 =
            let uu____4124 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____4124) in
          let uu____4125 =
            let uu____4132 =
              let uu____4137 =
                json_of_opt (fun _0_48  -> FStar_Util.JsonStr _0_48)
                  opt.opt_documentation in
              ("documentation", uu____4137) in
            let uu____4138 =
              let uu____4145 =
                let uu____4150 =
                  let uu____4151 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____4151 in
                ("type", uu____4150) in
              [uu____4145;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____4132 :: uu____4138 in
          uu____4119 :: uu____4125 in
        uu____4106 :: uu____4112 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____4099 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____4092
let json_of_fstar_option: fstar_option -> FStar_Util.json =
  fun opt  ->
    let uu____4188 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____4188
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____4200 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____4200);
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
  fun uu____4262  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____4265 =
        FStar_List.map (fun _0_49  -> FStar_Util.JsonStr _0_49)
          interactive_protocol_features in
      FStar_Util.JsonList uu____4265 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: alist_of_protocol_info))
let sig_of_fstar_option:
  Prims.string -> FStar_Options.opt_type -> Prims.string =
  fun name  ->
    fun typ  ->
      let flag = Prims.strcat "--" name in
      let uu____4281 = FStar_Options.desc_of_opt_type typ in
      match uu____4281 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.strcat flag (Prims.strcat " " arg_sig)
let fstar_options_list_cache: fstar_option Prims.list =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____4290 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____4319  ->
            match uu____4319 with
            | (_shortname,name,typ,doc1) ->
                let uu____4334 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____4334
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____4346 = sig_of_fstar_option name typ in
                        let uu____4347 = snippets_of_fstar_option name typ in
                        let uu____4350 =
                          let uu____4351 = FStar_Options.settable name in
                          if uu____4351
                          then OptSet
                          else
                            (let uu____4353 = FStar_Options.resettable name in
                             if uu____4353 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____4346;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____4347;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____4350
                        })))) in
  FStar_All.pipe_right uu____4290
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
    let uu___262_4378 = opt in
    let uu____4379 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___262_4378.opt_name);
      opt_sig = (uu___262_4378.opt_sig);
      opt_value = uu____4379;
      opt_default = (uu___262_4378.opt_default);
      opt_type = (uu___262_4378.opt_type);
      opt_snippets = (uu___262_4378.opt_snippets);
      opt_documentation = (uu___262_4378.opt_documentation);
      opt_permission_level = (uu___262_4378.opt_permission_level)
    }
let current_fstar_options:
  (fstar_option -> Prims.bool) -> fstar_option Prims.list =
  fun filter1  ->
    let uu____4391 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____4391
let trim_option_name:
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun opt_name  ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____4407 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____4407)
    else ("", opt_name)
let json_of_repl_state: repl_state -> FStar_Util.json =
  fun st  ->
    let filenames uu____4422 =
      match uu____4422 with
      | (task,uu____4430) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | PushFragment uu____4437 -> []) in
    let uu____4438 =
      let uu____4445 =
        let uu____4450 =
          let uu____4451 =
            let uu____4454 =
              FStar_List.concatMap filenames st.repl_deps_stack in
            FStar_List.map (fun _0_50  -> FStar_Util.JsonStr _0_50)
              uu____4454 in
          FStar_Util.JsonList uu____4451 in
        ("loaded-dependencies", uu____4450) in
      let uu____4461 =
        let uu____4468 =
          let uu____4473 =
            let uu____4474 =
              let uu____4477 =
                current_fstar_options (fun uu____4482  -> true) in
              FStar_List.map json_of_fstar_option uu____4477 in
            FStar_Util.JsonList uu____4474 in
          ("options", uu____4473) in
        [uu____4468] in
      uu____4445 :: uu____4461 in
    FStar_Util.JsonAssoc uu____4438
let with_printed_effect_args:
  'Auu____4499 . (Prims.unit -> 'Auu____4499) -> 'Auu____4499 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____4511  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____4522  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____4528  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____4535 'Auu____4536 .
    'Auu____4536 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4535,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____4567 'Auu____4568 .
    'Auu____4568 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4568,'Auu____4567) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____4597 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4597) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4614 =
      let uu____4619 = json_of_repl_state st in (QueryOK, uu____4619) in
    (uu____4614, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____4636 'Auu____4637 .
    'Auu____4637 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4637,'Auu____4636) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error:
  'Auu____4674 'Auu____4675 .
    'Auu____4675 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4675,'Auu____4674) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let run_vfs_add:
  'Auu____4712 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____4712) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop:
  'Auu____4755 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4755) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4772 = nothing_left_to_pop st in
    if uu____4772
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let st' = pop_repl st in
       ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))
let collect_errors: Prims.unit -> FStar_Errors.issue Prims.list =
  fun uu____4808  ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let load_deps:
  repl_state ->
    ((repl_state,Prims.string Prims.list) FStar_Pervasives_Native.tuple2,
      repl_state) FStar_Util.either
  =
  fun st  ->
    let uu____4827 =
      with_captured_errors st.repl_env
        (fun _env  ->
           let uu____4849 = deps_and_repl_ld_tasks_of_our_file st.repl_fname in
           FStar_All.pipe_left
             (fun _0_51  -> FStar_Pervasives_Native.Some _0_51) uu____4849) in
    match uu____4827 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks) ->
        let uu____4926 = run_repl_ld_transactions st tasks in
        (match uu____4926 with
         | FStar_Util.Inr st1 -> FStar_Util.Inr st1
         | FStar_Util.Inl st1 -> FStar_Util.Inl (st1, deps))
let rephrase_dependency_error: FStar_Errors.issue -> FStar_Errors.issue =
  fun issue  ->
    let uu___263_4961 = issue in
    let uu____4962 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____4962;
      FStar_Errors.issue_level = (uu___263_4961.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___263_4961.FStar_Errors.issue_range)
    }
let run_push_without_deps:
  'Auu____4969 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4969) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let uu____4990 = query in
      match uu____4990 with
      | { push_kind; push_code = text1; push_line = line;
          push_column = column; push_peek_only = peek_only;_} ->
          (FStar_TypeChecker_Env.toggle_id_info st.repl_env true;
           (let frag =
              {
                FStar_Parser_ParseIt.frag_text = text1;
                FStar_Parser_ParseIt.frag_line = line;
                FStar_Parser_ParseIt.frag_col = column
              } in
            let uu____5010 =
              run_repl_transaction st push_kind peek_only (PushFragment frag) in
            match uu____5010 with
            | (success,st1) ->
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____5032 =
                    let uu____5035 = collect_errors () in
                    FStar_All.pipe_right uu____5035
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____5032 in
                let st2 =
                  if success
                  then
                    let uu___264_5043 = st1 in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___264_5043.repl_fname);
                      repl_deps_stack = (uu___264_5043.repl_deps_stack);
                      repl_curmod = (uu___264_5043.repl_curmod);
                      repl_env = (uu___264_5043.repl_env);
                      repl_stdin = (uu___264_5043.repl_stdin);
                      repl_names = (uu___264_5043.repl_names)
                    }
                  else st1 in
                ((status, json_errors), (FStar_Util.Inl st2))))
let capitalize: Prims.string -> Prims.string =
  fun str  ->
    if str = ""
    then str
    else
      (let first =
         FStar_String.substring str (Prims.parse_int "0")
           (Prims.parse_int "1") in
       let uu____5059 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1")) in
       Prims.strcat (FStar_String.uppercase first) uu____5059)
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
          let uu____5086 = FStar_Util.psmap_empty () in
          let uu____5089 =
            let uu____5092 = FStar_Options.prims () in uu____5092 :: deps in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____5102 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____5102 true) uu____5086
            uu____5089 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____5118  ->
               match uu____5118 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____5130 = capitalize modname in
                        FStar_Util.split uu____5130 "." in
                      let uu____5131 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____5131 mod_path ns_query)) table
          (FStar_List.rev mods)
let run_push_with_deps:
  'Auu____5142 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5142) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      (let uu____5164 = FStar_Options.debug_any () in
       if uu____5164
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____5167 = load_deps st in
       match uu____5167 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____5200 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____5200 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____5231 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____5231 FStar_Pervasives.ignore);
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names in
             run_push_without_deps
               (let uu___265_5234 = st1 in
                {
                  repl_line = (uu___265_5234.repl_line);
                  repl_column = (uu___265_5234.repl_column);
                  repl_fname = (uu___265_5234.repl_fname);
                  repl_deps_stack = (uu___265_5234.repl_deps_stack);
                  repl_curmod = (uu___265_5234.repl_curmod);
                  repl_env = (uu___265_5234.repl_env);
                  repl_stdin = (uu___265_5234.repl_stdin);
                  repl_names = names1
                }) query)))
let run_push:
  'Auu____5241 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5241) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let uu____5262 = nothing_left_to_pop st in
      if uu____5262
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
              let uu____5344 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".") in
              FStar_Ident.lid_of_ids uu____5344 in
            let lid1 =
              let uu____5348 =
                FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____5348 in
            let uu____5353 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
            FStar_All.pipe_right uu____5353
              (FStar_Util.map_option
                 (fun uu____5408  ->
                    match uu____5408 with
                    | ((uu____5427,typ),r) -> ((FStar_Util.Inr lid1), typ, r))) in
          let docs_of_lid lid =
            let uu____5444 =
              FStar_ToSyntax_Env.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid in
            FStar_All.pipe_right uu____5444
              (FStar_Util.map_option FStar_Pervasives_Native.fst) in
          let def_of_lid lid =
            let uu____5473 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
            FStar_Util.bind_opt uu____5473
              (fun uu___249_5517  ->
                 match uu___249_5517 with
                 | (FStar_Util.Inr (se,uu____5539),uu____5540) ->
                     let uu____5569 = sigelt_to_string se in
                     FStar_Pervasives_Native.Some uu____5569
                 | uu____5570 -> FStar_Pervasives_Native.None) in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____5622  ->
                 match uu____5622 with
                 | (file,row,col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____5669 -> info_at_pos_opt
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
                    let uu____5797 = term_to_string tcenv typ in
                    FStar_Pervasives_Native.Some uu____5797
                  else FStar_Pervasives_Native.None in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____5805 -> FStar_Pervasives_Native.None in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____5816 -> FStar_Pervasives_Native.None in
                let def_range =
                  if FStar_List.mem "defined-at" requested_info
                  then FStar_Pervasives_Native.Some rng
                  else FStar_Pervasives_Native.None in
                let result =
                  {
                    slr_name = name;
                    slr_def_range = def_range;
                    slr_typ = typ_str;
                    slr_doc = doc_str;
                    slr_def = def_str
                  } in
                let uu____5828 =
                  let uu____5839 = alist_of_symbol_lookup_result result in
                  ("symbol", uu____5839) in
                FStar_Pervasives_Native.Some uu____5828 in
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
    let uu____5945 = trim_option_name opt_name in
    match uu____5945 with
    | (uu____5964,trimmed_name) ->
        let uu____5966 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____5966 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.strcat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____5994 =
               let uu____6005 =
                 let uu____6012 = update_option opt in
                 alist_of_fstar_option uu____6012 in
               ("option", uu____6005) in
             FStar_Util.Inr uu____5994)
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
      let uu____6054 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query in
      match uu____6054 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____6082 =
            let uu____6093 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____6093) in
          FStar_Util.Inr uu____6082
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____6117 =
            let uu____6128 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____6128) in
          FStar_Util.Inr uu____6117
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
          let uu____6201 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____6201 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____6261 ->
              let uu____6272 = run_module_lookup st symbol in
              (match uu____6272 with
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
  'Auu____6433 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6433) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____6486 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____6486 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let code_autocomplete_mod_filter:
  'Auu____6572 .
    ('Auu____6572,FStar_Interactive_CompletionTable.mod_symbol)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____6572,FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu___250_6586  ->
    match uu___250_6586 with
    | (uu____6591,FStar_Interactive_CompletionTable.Namespace uu____6592) ->
        FStar_Pervasives_Native.None
    | (uu____6597,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____6598;
         FStar_Interactive_CompletionTable.mod_path = uu____6599;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____6606 =
          let uu____6611 =
            let uu____6612 =
              let uu___266_6613 = md in
              let uu____6614 =
                let uu____6615 =
                  FStar_Interactive_CompletionTable.mod_name md in
                Prims.strcat uu____6615 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____6614;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___266_6613.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___266_6613.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____6612 in
          (pth, uu____6611) in
        FStar_Pervasives_Native.Some uu____6606
let run_code_autocomplete:
  'Auu____6626 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6626) FStar_Util.either)
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
  'Auu____6681 'Auu____6682 'Auu____6683 .
    repl_state ->
      Prims.string ->
        'Auu____6683 ->
          'Auu____6682 ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____6681) FStar_Util.either)
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
              (fun _0_52  -> FStar_Pervasives_Native.Some _0_52) in
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
        let uu____6747 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only") in
        match uu____6747 with
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
  'Auu____6779 'Auu____6780 .
    'Auu____6780 ->
      Prims.string ->
        Prims.bool ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            ('Auu____6780,'Auu____6779) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____6805 = trim_option_name search_term in
        match uu____6805 with
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
        | (uu____6856,uu____6857) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete:
  'Auu____6874 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____6874) FStar_Util.either)
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
let run_compute:
  'Auu____6910 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____6910) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let run_and_rewind st1 task =
          let env' = push st1.repl_env "#compute" in
          let results = task st1 in
          pop env' "#compute"; (results, (FStar_Util.Inl st1)) in
        let dummy_let_fragment term1 =
          let dummy_decl =
            FStar_Util.format1 "let __compute_dummy__ = (%s)" term1 in
          {
            FStar_Parser_ParseIt.frag_text = dummy_decl;
            FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
            FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
          } in
        let normalize_term1 tcenv rules1 t =
          FStar_TypeChecker_Normalize.normalize rules1 tcenv t in
        let find_let_body ses =
          match ses with
          | {
              FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                ((uu____7033,{ FStar_Syntax_Syntax.lbname = uu____7034;
                               FStar_Syntax_Syntax.lbunivs = univs1;
                               FStar_Syntax_Syntax.lbtyp = uu____7036;
                               FStar_Syntax_Syntax.lbeff = uu____7037;
                               FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____7039);
              FStar_Syntax_Syntax.sigrng = uu____7040;
              FStar_Syntax_Syntax.sigquals = uu____7041;
              FStar_Syntax_Syntax.sigmeta = uu____7042;
              FStar_Syntax_Syntax.sigattrs = uu____7043;_}::[] ->
              FStar_Pervasives_Native.Some (univs1, def)
          | uu____7082 -> FStar_Pervasives_Native.None in
        let parse1 frag =
          let uu____7101 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
          match uu____7101 with
          | FStar_Util.Inl (FStar_Util.Inr decls,uu____7125) ->
              FStar_Pervasives_Native.Some decls
          | uu____7170 -> FStar_Pervasives_Native.None in
        let desugar env decls =
          let uu____7202 =
            let uu____7207 = FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
            uu____7207 env.FStar_TypeChecker_Env.dsenv in
          FStar_Pervasives_Native.fst uu____7202 in
        let typecheck tcenv decls =
          let uu____7225 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
          match uu____7225 with | (ses,uu____7239,uu____7240) -> ses in
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
        run_and_rewind st
          (fun st1  ->
             let tcenv = st1.repl_env in
             let frag = dummy_let_fragment term in
             match st1.repl_curmod with
             | FStar_Pervasives_Native.None  ->
                 (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
             | uu____7272 ->
                 let uu____7273 = parse1 frag in
                 (match uu____7273 with
                  | FStar_Pervasives_Native.None  ->
                      (QueryNOK,
                        (FStar_Util.JsonStr "Could not parse this term"))
                  | FStar_Pervasives_Native.Some decls ->
                      let aux uu____7296 =
                        let decls1 = desugar tcenv decls in
                        let ses = typecheck tcenv decls1 in
                        match find_let_body ses with
                        | FStar_Pervasives_Native.None  ->
                            (QueryNOK,
                              (FStar_Util.JsonStr
                                 "Typechecking yielded an unexpected term"))
                        | FStar_Pervasives_Native.Some (univs1,def) ->
                            let uu____7331 =
                              FStar_Syntax_Subst.open_univ_vars univs1 def in
                            (match uu____7331 with
                             | (univs2,def1) ->
                                 let tcenv1 =
                                   FStar_TypeChecker_Env.push_univ_vars tcenv
                                     univs2 in
                                 let normalized =
                                   normalize_term1 tcenv1 rules1 def1 in
                                 let uu____7344 =
                                   let uu____7345 =
                                     term_to_string tcenv1 normalized in
                                   FStar_Util.JsonStr uu____7345 in
                                 (QueryOK, uu____7344)) in
                      let uu____7346 = FStar_Options.trace_error () in
                      if uu____7346
                      then aux ()
                      else
                        (try aux ()
                         with
                         | e ->
                             let uu____7371 =
                               let uu____7372 = FStar_Errors.issue_of_exn e in
                               match uu____7372 with
                               | FStar_Pervasives_Native.Some issue ->
                                   let uu____7376 =
                                     FStar_Errors.format_issue issue in
                                   FStar_Util.JsonStr uu____7376
                               | FStar_Pervasives_Native.None  ->
                                   FStar_Exn.raise e in
                             (QueryNOK, uu____7371))))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid[@@deriving show]
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}[@@deriving show]
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____7398 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____7412 -> false
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
  fun uu___251_7436  ->
    match uu___251_7436 with
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
    let uu____7604 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____7611 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____7604; sc_fvars = uu____7611 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____7660 = FStar_ST.op_Bang sc.sc_typ in
      match uu____7660 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____7717 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____7717 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7738,typ),uu____7740) ->
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
      let uu____7816 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____7816 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____7887 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____7887 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let json_of_search_result:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____7954 = sc_typ tcenv sc in term_to_string tcenv uu____7954 in
      let uu____7955 =
        let uu____7962 =
          let uu____7967 =
            let uu____7968 =
              let uu____7969 =
                FStar_ToSyntax_Env.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              uu____7969.FStar_Ident.str in
            FStar_Util.JsonStr uu____7968 in
          ("lid", uu____7967) in
        [uu____7962; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____7955
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____7989 -> true
    | uu____7990 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____7998 -> uu____7998
let run_search:
  'Auu____8005 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____8005) FStar_Util.either)
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
              let uu____8040 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____8040 in
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
              let uu____8064 =
                let uu____8065 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____8065 in
              FStar_Exn.raise uu____8064
            else
              if beg_quote
              then
                (let uu____8067 = strip_quotes term1 in
                 NameContainsStr uu____8067)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____8070 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____8070 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____8073 =
                       let uu____8074 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____8074 in
                     FStar_Exn.raise uu____8073
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____8090 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.strcat (if term.st_negate then "-" else "") uu____8090 in
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
                let uu____8153 = FStar_List.map pprint_one terms in
                FStar_Util.concat_l " " uu____8153 in
              let uu____8156 =
                let uu____8157 =
                  FStar_Util.format1 "No results found for query [%s]" kwds in
                InvalidSearch uu____8157 in
              FStar_Exn.raise uu____8156
          | uu____8162 -> (QueryOK, (FStar_Util.JsonList js))
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
          { push_kind = SyntaxCheck ; push_code = uu____8255;
            push_line = uu____8256; push_column = uu____8257;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____8258 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____8259 -> q)
let rec go: repl_state -> Prims.int =
  fun st  ->
    let rec loop st1 =
      let query =
        let uu____8269 = read_interactive_query st1.repl_stdin in
        validate_query st1 uu____8269 in
      let uu____8270 = run_query st1 query.qq in
      match uu____8270 with
      | ((status,response),state_opt) ->
          (write_response query.qid status response;
           (match state_opt with
            | FStar_Util.Inl st' -> loop st'
            | FStar_Util.Inr exitcode -> FStar_Exn.raise (ExitREPL exitcode))) in
    let uu____8301 = FStar_Options.trace_error () in
    if uu____8301 then loop st else (try loop st with | ExitREPL n1 -> n1)
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____8320 =
      let uu____8323 = FStar_ST.op_Bang issues in e :: uu____8323 in
    FStar_ST.op_Colon_Equals issues uu____8320 in
  let count_errors uu____8457 =
    let uu____8458 =
      let uu____8461 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____8461 in
    FStar_List.length uu____8458 in
  let report1 uu____8535 =
    let uu____8536 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8536 in
  let clear1 uu____8606 = FStar_ST.op_Colon_Equals issues [] in
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
             let uu____8693 = get_json () in write_message label1 uu____8693)
  }
let initial_range: FStar_Range.range =
  let uu____8694 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  let uu____8695 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  FStar_Range.mk_range "<input>" uu____8694 uu____8695
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let env = FStar_Universal.init_env () in
     let env1 = FStar_TypeChecker_Env.set_range env initial_range in
     let init_st =
       let uu____8704 = FStar_Util.open_stdin () in
       {
         repl_line = (Prims.parse_int "1");
         repl_column = (Prims.parse_int "0");
         repl_fname = filename;
         repl_deps_stack = [];
         repl_curmod = FStar_Pervasives_Native.None;
         repl_env = env1;
         repl_stdin = uu____8704;
         repl_names = FStar_Interactive_CompletionTable.empty
       } in
     let exit_code =
       let uu____8710 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____8710
       then
         let uu____8711 =
           let uu____8712 = FStar_Options.file_list () in
           FStar_List.hd uu____8712 in
         FStar_SMTEncoding_Solver.with_hints_db uu____8711
           (fun uu____8716  -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    (let uu____8724 =
       let uu____8725 = FStar_Options.codegen () in
       FStar_Option.isSome uu____8725 in
     if uu____8724
     then
       FStar_Util.print_warning
         "code-generation is not supported in interactive mode, ignoring the codegen flag"
     else ());
    (let uu____8729 = FStar_Options.trace_error () in
     if uu____8729
     then interactive_mode' filename
     else
       (try
          FStar_Errors.set_handler interactive_error_handler;
          interactive_mode' filename
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))