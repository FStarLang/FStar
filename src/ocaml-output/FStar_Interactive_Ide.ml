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
      let uu___376_49 = env in
      let uu____50 =
        FStar_ToSyntax_Env.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck) in
      {
        FStar_TypeChecker_Env.solver =
          (uu___376_49.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___376_49.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___376_49.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___376_49.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___376_49.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___376_49.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___376_49.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___376_49.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___376_49.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___376_49.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___376_49.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___376_49.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___376_49.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___376_49.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___376_49.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___376_49.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___376_49.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___376_49.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___376_49.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___376_49.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___376_49.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___376_49.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___376_49.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___376_49.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___376_49.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___376_49.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___376_49.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___376_49.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___376_49.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___376_49.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___376_49.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____50;
        FStar_TypeChecker_Env.dep_graph =
          (uu___376_49.FStar_TypeChecker_Env.dep_graph)
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
            FStar_Errors.maybe_fatal_error uu____90
              (FStar_Errors.AssertionFailure, msg1));
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
    let uu____568 = FStar_ST.op_Bang repl_stack in
    match uu____568 with
    | [] -> failwith "Too many pops"
    | (uu____637,st')::stack ->
        (pop st.repl_env "#pop";
         FStar_ST.op_Colon_Equals repl_stack stack;
         st')
let push_repl:
  push_kind -> repl_task -> repl_state -> FStar_TypeChecker_Env.env =
  fun push_kind  ->
    fun task  ->
      fun st  ->
        (let uu____720 =
           let uu____727 = FStar_ST.op_Bang repl_stack in (task, st) ::
             uu____727 in
         FStar_ST.op_Colon_Equals repl_stack uu____720);
        (let uu____854 = set_check_kind st.repl_env push_kind in
         push uu____854 "")
let nothing_left_to_pop: repl_state -> Prims.bool =
  fun st  ->
    let uu____858 =
      let uu____859 = FStar_ST.op_Bang repl_stack in
      FStar_List.length uu____859 in
    uu____858 = (FStar_List.length st.repl_deps_stack)
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
    match projectee with | NTAlias _0 -> true | uu____976 -> false
let __proj__NTAlias__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | NTAlias _0 -> _0
let uu___is_NTOpen: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____1010 -> false
let __proj__NTOpen__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTOpen _0 -> _0
let uu___is_NTInclude: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____1038 -> false
let __proj__NTInclude__item___0:
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTInclude _0 -> _0
let uu___is_NTBinding: name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____1062 -> false
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
              let uu____1096 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_alias table
                (FStar_Ident.text_of_id id) [] uu____1096
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____1105 = query_of_lid included in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_ToSyntax_Env.Open_module) [] uu____1105
            else table
        | NTInclude (host,included) ->
            let uu____1109 =
              if is_cur_mod host then [] else query_of_lid host in
            let uu____1111 = query_of_lid included in
            FStar_Interactive_CompletionTable.register_include table
              uu____1109 uu____1111
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_TypeChecker_Env.Binding_lid (lid,uu____1119) -> [lid]
              | FStar_TypeChecker_Env.Binding_sig (lids,uu____1121) -> lids
              | FStar_TypeChecker_Env.Binding_sig_inst
                  (lids,uu____1127,uu____1128) -> lids
              | uu____1133 -> [] in
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
              let uu____1164 = FStar_Syntax_Syntax.mod_name md in
              uu____1164.FStar_Ident.str in
        let updater = update_names_from_event cur_mod_str in
        FStar_List.fold_left updater names1 name_events
let commit_name_tracking:
  repl_state -> name_tracking_event Prims.list -> repl_state =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events in
      let uu___379_1181 = st in
      {
        repl_line = (uu___379_1181.repl_line);
        repl_column = (uu___379_1181.repl_column);
        repl_fname = (uu___379_1181.repl_fname);
        repl_deps_stack = (uu___379_1181.repl_deps_stack);
        repl_curmod = (uu___379_1181.repl_curmod);
        repl_env = (uu___379_1181.repl_env);
        repl_stdin = (uu___379_1181.repl_stdin);
        repl_names = names1
      }
let fresh_name_tracking_hooks:
  Prims.unit ->
    (name_tracking_event Prims.list FStar_ST.ref,FStar_ToSyntax_Env.dsenv_hooks,
      FStar_TypeChecker_Env.tcenv_hooks) FStar_Pervasives_Native.tuple3
  =
  fun uu____1194  ->
    let events = FStar_Util.mk_ref [] in
    let push_event evt =
      let uu____1206 =
        let uu____1209 = FStar_ST.op_Bang events in evt :: uu____1209 in
      FStar_ST.op_Colon_Equals events uu____1206 in
    (events,
      {
        FStar_ToSyntax_Env.ds_push_open_hook =
          (fun dsenv  ->
             fun op  ->
               let uu____1366 =
                 let uu____1367 =
                   let uu____1372 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____1372, op) in
                 NTOpen uu____1367 in
               push_event uu____1366);
        FStar_ToSyntax_Env.ds_push_include_hook =
          (fun dsenv  ->
             fun ns  ->
               let uu____1378 =
                 let uu____1379 =
                   let uu____1384 = FStar_ToSyntax_Env.current_module dsenv in
                   (uu____1384, ns) in
                 NTInclude uu____1379 in
               push_event uu____1378);
        FStar_ToSyntax_Env.ds_push_module_abbrev_hook =
          (fun dsenv  ->
             fun x  ->
               fun l  ->
                 let uu____1392 =
                   let uu____1393 =
                     let uu____1400 = FStar_ToSyntax_Env.current_module dsenv in
                     (uu____1400, x, l) in
                   NTAlias uu____1393 in
                 push_event uu____1392)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1405  -> fun s  -> push_event (NTBinding s))
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
      let uu____1444 =
        FStar_Universal.with_tcenv env1
          (fun dsenv  ->
             let uu____1452 = FStar_ToSyntax_Env.set_ds_hooks dsenv dshooks in
             ((), uu____1452)) in
      match uu____1444 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks in
    let uu____1454 =
      let uu____1459 =
        FStar_ToSyntax_Env.ds_hooks env.FStar_TypeChecker_Env.dsenv in
      let uu____1460 = FStar_TypeChecker_Env.tc_hooks env in
      (uu____1459, uu____1460) in
    match uu____1454 with
    | (old_dshooks,old_tchooks) ->
        let uu____1475 = fresh_name_tracking_hooks () in
        (match uu____1475 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____1509 = set_hooks new_dshooks new_tchooks env in
             (uu____1509,
               ((fun env1  ->
                   let uu____1522 = set_hooks old_dshooks old_tchooks env1 in
                   let uu____1523 =
                     let uu____1526 = FStar_ST.op_Bang events in
                     FStar_List.rev uu____1526 in
                   (uu____1522, uu____1523)))))
let string_of_repl_task: repl_task -> Prims.string =
  fun uu___361_1597  ->
    match uu___361_1597 with
    | LDInterleaved (intf,impl) ->
        let uu____1600 = string_of_timed_fname intf in
        let uu____1601 = string_of_timed_fname impl in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1600 uu____1601
    | LDSingle intf_or_impl ->
        let uu____1603 = string_of_timed_fname intf_or_impl in
        FStar_Util.format1 "LDSingle %s" uu____1603
    | LDInterfaceOfCurrentFile intf ->
        let uu____1605 = string_of_timed_fname intf in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1605
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
        let uu____1620 = FStar_Universal.tc_one_file env intf_opt modf in
        match uu____1620 with | (uu____1629,env1) -> env1
let run_repl_task:
  optmod_t ->
    env_t -> repl_task -> (optmod_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____1658 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname in
            (curmod, uu____1658)
        | LDSingle intf_or_impl ->
            let uu____1660 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname in
            (curmod, uu____1660)
        | LDInterfaceOfCurrentFile intf ->
            let uu____1662 =
              FStar_Universal.load_interface_decls env intf.tf_fname in
            (curmod, uu____1662)
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
            let uu____1707 = aux deps' final_tasks1 in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____1707
        | intf_or_impl::deps' ->
            let uu____1714 = aux deps' final_tasks1 in
            (LDSingle (wrap intf_or_impl)) :: uu____1714
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
      let uu____1749 = get_mod_name f in uu____1749 = our_mod_name in
    let uu____1750 = FStar_Dependencies.find_deps_if_needed [filename] in
    match uu____1750 with
    | (deps,dep_graph1) ->
        let uu____1773 = FStar_List.partition has_our_mod_name deps in
        (match uu____1773 with
         | (same_name,real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____1810 =
                       let uu____1811 = FStar_Parser_Dep.is_interface intf in
                       Prims.op_Negation uu____1811 in
                     if uu____1810
                     then
                       let uu____1812 =
                         let uu____1817 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf in
                         (FStar_Errors.MissingInterface, uu____1817) in
                       FStar_Errors.raise_err uu____1812
                     else ());
                    (let uu____1820 =
                       let uu____1821 =
                         FStar_Parser_Dep.is_implementation impl in
                       Prims.op_Negation uu____1821 in
                     if uu____1820
                     then
                       let uu____1822 =
                         let uu____1827 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl in
                         (FStar_Errors.MissingImplementation, uu____1827) in
                       FStar_Errors.raise_err uu____1822
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____1830 ->
                   let mods_str = FStar_String.concat " " same_name in
                   let message = "Too many or too few files matching %s: %s" in
                   ((let uu____1836 =
                       let uu____1841 =
                         FStar_Util.format2 message our_mod_name mods_str in
                       (FStar_Errors.TooManyOrTooFewFileMatch, uu____1841) in
                     FStar_Errors.raise_err uu____1836);
                    []) in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks in
             (real_deps, tasks, dep_graph1))
let update_task_timestamps: repl_task -> repl_task =
  fun uu___362_1851  ->
    match uu___362_1851 with
    | LDInterleaved (intf,impl) ->
        let uu____1854 =
          let uu____1859 = tf_of_fname intf.tf_fname in
          let uu____1860 = tf_of_fname impl.tf_fname in
          (uu____1859, uu____1860) in
        LDInterleaved uu____1854
    | LDSingle intf_or_impl ->
        let uu____1862 = tf_of_fname intf_or_impl.tf_fname in
        LDSingle uu____1862
    | LDInterfaceOfCurrentFile intf ->
        let uu____1864 = tf_of_fname intf.tf_fname in
        LDInterfaceOfCurrentFile uu____1864
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
          let uu____1883 = track_name_changes env in
          match uu____1883 with
          | (env1,finish_name_tracking) ->
              let check_success uu____1921 =
                (let uu____1924 = FStar_Errors.get_err_count () in
                 uu____1924 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback) in
              let uu____1925 =
                let uu____1932 =
                  with_captured_errors env1
                    (fun env2  ->
                       let uu____1946 =
                         run_repl_task st.repl_curmod env2 task in
                       FStar_All.pipe_left
                         (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
                         uu____1946) in
                match uu____1932 with
                | FStar_Pervasives_Native.Some (curmod,env2) when
                    check_success () -> (curmod, env2, true)
                | uu____1977 -> ((st.repl_curmod), env1, false) in
              (match uu____1925 with
               | (curmod,env2,success) ->
                   let uu____1991 = finish_name_tracking env2 in
                   (match uu____1991 with
                    | (env',name_events) ->
                        let st1 =
                          let uu___380_2009 = st in
                          {
                            repl_line = (uu___380_2009.repl_line);
                            repl_column = (uu___380_2009.repl_column);
                            repl_fname = (uu___380_2009.repl_fname);
                            repl_deps_stack = (uu___380_2009.repl_deps_stack);
                            repl_curmod = curmod;
                            repl_env = env2;
                            repl_stdin = (uu___380_2009.repl_stdin);
                            repl_names = (uu___380_2009.repl_names)
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
        let uu____2033 = FStar_Options.debug_any () in
        if uu____2033
        then
          let uu____2034 = string_of_repl_task task in
          FStar_Util.print2 "%s %s" verb uu____2034
        else () in
      let rec revert_many st1 uu___363_2048 =
        match uu___363_2048 with
        | [] -> st1
        | (task,_st')::entries ->
            ((let uu____2073 = Obj.magic () in ());
             debug1 "Reverting" task;
             (let uu____2075 = pop_repl st1 in revert_many uu____2075 entries)) in
      let rec aux st1 tasks1 previous =
        match (tasks1, previous) with
        | ([],[]) -> FStar_Util.Inl st1
        | (task::tasks2,[]) ->
            (debug1 "Loading" task;
             (let uu____2120 = FStar_Options.restore_cmd_line_options false in
              FStar_All.pipe_right uu____2120 FStar_Pervasives.ignore);
             (let timestamped_task = update_task_timestamps task in
              let push_kind =
                let uu____2123 = FStar_Options.lax () in
                if uu____2123 then LaxCheck else FullCheck in
              let uu____2125 =
                run_repl_transaction st1 push_kind false timestamped_task in
              match uu____2125 with
              | (success,st2) ->
                  if success
                  then
                    let uu____2140 =
                      let uu___381_2141 = st2 in
                      let uu____2142 = FStar_ST.op_Bang repl_stack in
                      {
                        repl_line = (uu___381_2141.repl_line);
                        repl_column = (uu___381_2141.repl_column);
                        repl_fname = (uu___381_2141.repl_fname);
                        repl_deps_stack = uu____2142;
                        repl_curmod = (uu___381_2141.repl_curmod);
                        repl_env = (uu___381_2141.repl_env);
                        repl_stdin = (uu___381_2141.repl_stdin);
                        repl_names = (uu___381_2141.repl_names)
                      } in
                    aux uu____2140 tasks2 []
                  else FStar_Util.Inr st2))
        | (task::tasks2,prev::previous1) when
            let uu____2220 = update_task_timestamps task in
            (FStar_Pervasives_Native.fst prev) = uu____2220 ->
            (debug1 "Skipping" task; aux st1 tasks2 previous1)
        | (tasks2,previous1) ->
            let uu____2232 = revert_many st1 previous1 in
            aux uu____2232 tasks2 [] in
      aux st tasks (FStar_List.rev st.repl_deps_stack)
let json_to_str: FStar_Util.json -> Prims.string =
  fun uu___364_2239  ->
    match uu___364_2239 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2243 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2243
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2245 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2248 -> "dictionary (...)"
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2
let uu___is_UnexpectedJsonType: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____2265 -> true
    | uu____2270 -> false
let __proj__UnexpectedJsonType__item__uu___:
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____2285 -> uu____2285
let js_fail: 'Auu____2293 . Prims.string -> FStar_Util.json -> 'Auu____2293 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let js_int: FStar_Util.json -> Prims.int =
  fun uu___365_2304  ->
    match uu___365_2304 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let js_str: FStar_Util.json -> Prims.string =
  fun uu___366_2309  ->
    match uu___366_2309 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list:
  'Auu____2315 .
    (FStar_Util.json -> 'Auu____2315) ->
      FStar_Util.json -> 'Auu____2315 Prims.list
  =
  fun k  ->
    fun uu___367_2328  ->
      match uu___367_2328 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let js_assoc:
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___368_2345  ->
    match uu___368_2345 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let js_pushkind: FStar_Util.json -> push_kind =
  fun s  ->
    let uu____2369 = js_str s in
    match uu____2369 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____2370 -> js_fail "push_kind" s
let js_reductionrule: FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____2374 = js_str s in
    match uu____2374 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____2375 -> js_fail "reduction rule" s
type completion_context =
  | CKCode
  | CKOption of Prims.bool
  | CKModuleOrNamespace of (Prims.bool,Prims.bool)
  FStar_Pervasives_Native.tuple2[@@deriving show]
let uu___is_CKCode: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____2391 -> false
let uu___is_CKOption: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____2396 -> false
let __proj__CKOption__item___0: completion_context -> Prims.bool =
  fun projectee  -> match projectee with | CKOption _0 -> _0
let uu___is_CKModuleOrNamespace: completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____2412 -> false
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
        let uu____2440 = js_str k1 in
        (match uu____2440 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____2441 ->
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
    match projectee with | LKSymbolOnly  -> true | uu____2445 -> false
let uu___is_LKModule: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____2449 -> false
let uu___is_LKOption: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____2453 -> false
let uu___is_LKCode: lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____2457 -> false
let js_optional_lookup_context:
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2466 = js_str k1 in
        (match uu____2466 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____2467 ->
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
    match projectee with | Exit  -> true | uu____2551 -> false
let uu___is_DescribeProtocol: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____2555 -> false
let uu___is_DescribeRepl: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____2559 -> false
let uu___is_Segment: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____2564 -> false
let __proj__Segment__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Segment _0 -> _0
let uu___is_Pop: query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____2575 -> false
let uu___is_Push: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____2580 -> false
let __proj__Push__item___0: query' -> push_query =
  fun projectee  -> match projectee with | Push _0 -> _0
let uu___is_VfsAdd: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____2598 -> false
let __proj__VfsAdd__item___0:
  query' ->
    (Prims.string FStar_Pervasives_Native.option,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | VfsAdd _0 -> _0
let uu___is_AutoComplete: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____2632 -> false
let __proj__AutoComplete__item___0:
  query' -> (Prims.string,completion_context) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | AutoComplete _0 -> _0
let uu___is_Lookup: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2668 -> false
let __proj__Lookup__item___0:
  query' ->
    (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
      Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Lookup _0 -> _0
let uu___is_Compute: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2724 -> false
let __proj__Compute__item___0:
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0
let uu___is_Search: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2760 -> false
let __proj__Search__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0
let uu___is_GenericError: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____2772 -> false
let __proj__GenericError__item___0: query' -> Prims.string =
  fun projectee  -> match projectee with | GenericError _0 -> _0
let uu___is_ProtocolViolation: query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2784 -> false
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
  fun uu___369_2804  ->
    match uu___369_2804 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____2805 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____2806; push_code = uu____2807;
          push_line = uu____2808; push_column = uu____2809;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____2810 -> false
    | GenericError uu____2817 -> false
    | ProtocolViolation uu____2818 -> false
    | Push uu____2819 -> true
    | AutoComplete uu____2820 -> true
    | Lookup uu____2825 -> true
    | Compute uu____2838 -> true
    | Search uu____2847 -> true
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
    | InvalidQuery uu____2856 -> true
    | uu____2857 -> false
let __proj__InvalidQuery__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2864 -> uu____2864
type query_status =
  | QueryOK
  | QueryNOK
  | QueryViolatesProtocol[@@deriving show]
let uu___is_QueryOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2868 -> false
let uu___is_QueryNOK: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2872 -> false
let uu___is_QueryViolatesProtocol: query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2876 -> false
let try_assoc:
  'Auu____2881 'Auu____2882 .
    'Auu____2882 ->
      ('Auu____2882,'Auu____2881) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2881 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2905 =
        FStar_Util.try_find
          (fun uu____2919  ->
             match uu____2919 with | (k,uu____2925) -> k = key) a in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2905
let wrap_js_failure: Prims.string -> Prims.string -> FStar_Util.json -> query
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2939 =
          let uu____2940 =
            let uu____2941 = json_to_str got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2941 in
          ProtocolViolation uu____2940 in
        { qq = uu____2939; qid }
let unpack_interactive_query: FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2967 = try_assoc key a in
      match uu____2967 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2971 =
            let uu____2972 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc in
            InvalidQuery uu____2972 in
          FStar_Exn.raise uu____2971 in
    let request = FStar_All.pipe_right json js_assoc in
    let qid =
      let uu____2987 = assoc1 "query" "query-id" request in
      FStar_All.pipe_right uu____2987 js_str in
    try
      let query =
        let uu____2996 = assoc1 "query" "query" request in
        FStar_All.pipe_right uu____2996 js_str in
      let args =
        let uu____3004 = assoc1 "query" "args" request in
        FStar_All.pipe_right uu____3004 js_assoc in
      let arg k = assoc1 "[args]" k args in
      let try_arg k =
        let uu____3021 = try_assoc k args in
        match uu____3021 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other in
      let uu____3029 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "segment" ->
            let uu____3030 =
              let uu____3031 = arg "code" in
              FStar_All.pipe_right uu____3031 js_str in
            Segment uu____3030
        | "peek" ->
            let uu____3032 =
              let uu____3033 =
                let uu____3034 = arg "kind" in
                FStar_All.pipe_right uu____3034 js_pushkind in
              let uu____3035 =
                let uu____3036 = arg "code" in
                FStar_All.pipe_right uu____3036 js_str in
              let uu____3037 =
                let uu____3038 = arg "line" in
                FStar_All.pipe_right uu____3038 js_int in
              let uu____3039 =
                let uu____3040 = arg "column" in
                FStar_All.pipe_right uu____3040 js_int in
              {
                push_kind = uu____3033;
                push_code = uu____3035;
                push_line = uu____3037;
                push_column = uu____3039;
                push_peek_only = (query = "peek")
              } in
            Push uu____3032
        | "push" ->
            let uu____3041 =
              let uu____3042 =
                let uu____3043 = arg "kind" in
                FStar_All.pipe_right uu____3043 js_pushkind in
              let uu____3044 =
                let uu____3045 = arg "code" in
                FStar_All.pipe_right uu____3045 js_str in
              let uu____3046 =
                let uu____3047 = arg "line" in
                FStar_All.pipe_right uu____3047 js_int in
              let uu____3048 =
                let uu____3049 = arg "column" in
                FStar_All.pipe_right uu____3049 js_int in
              {
                push_kind = uu____3042;
                push_code = uu____3044;
                push_line = uu____3046;
                push_column = uu____3048;
                push_peek_only = (query = "peek")
              } in
            Push uu____3041
        | "autocomplete" ->
            let uu____3050 =
              let uu____3055 =
                let uu____3056 = arg "partial-symbol" in
                FStar_All.pipe_right uu____3056 js_str in
              let uu____3057 =
                let uu____3058 = try_arg "context" in
                FStar_All.pipe_right uu____3058
                  js_optional_completion_context in
              (uu____3055, uu____3057) in
            AutoComplete uu____3050
        | "lookup" ->
            let uu____3063 =
              let uu____3076 =
                let uu____3077 = arg "symbol" in
                FStar_All.pipe_right uu____3077 js_str in
              let uu____3078 =
                let uu____3079 = try_arg "context" in
                FStar_All.pipe_right uu____3079 js_optional_lookup_context in
              let uu____3084 =
                let uu____3093 =
                  let uu____3102 = try_arg "location" in
                  FStar_All.pipe_right uu____3102
                    (FStar_Util.map_option js_assoc) in
                FStar_All.pipe_right uu____3093
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____3160 =
                          let uu____3161 = assoc1 "[location]" "filename" loc in
                          FStar_All.pipe_right uu____3161 js_str in
                        let uu____3162 =
                          let uu____3163 = assoc1 "[location]" "line" loc in
                          FStar_All.pipe_right uu____3163 js_int in
                        let uu____3164 =
                          let uu____3165 = assoc1 "[location]" "column" loc in
                          FStar_All.pipe_right uu____3165 js_int in
                        (uu____3160, uu____3162, uu____3164))) in
              let uu____3166 =
                let uu____3169 = arg "requested-info" in
                FStar_All.pipe_right uu____3169 (js_list js_str) in
              (uu____3076, uu____3078, uu____3084, uu____3166) in
            Lookup uu____3063
        | "compute" ->
            let uu____3182 =
              let uu____3191 =
                let uu____3192 = arg "term" in
                FStar_All.pipe_right uu____3192 js_str in
              let uu____3193 =
                let uu____3198 = try_arg "rules" in
                FStar_All.pipe_right uu____3198
                  (FStar_Util.map_option (js_list js_reductionrule)) in
              (uu____3191, uu____3193) in
            Compute uu____3182
        | "search" ->
            let uu____3213 =
              let uu____3214 = arg "terms" in
              FStar_All.pipe_right uu____3214 js_str in
            Search uu____3213
        | "vfs-add" ->
            let uu____3215 =
              let uu____3222 =
                let uu____3225 = try_arg "filename" in
                FStar_All.pipe_right uu____3225
                  (FStar_Util.map_option js_str) in
              let uu____3232 =
                let uu____3233 = arg "contents" in
                FStar_All.pipe_right uu____3233 js_str in
              (uu____3222, uu____3232) in
            VfsAdd uu____3215
        | uu____3236 ->
            let uu____3237 = FStar_Util.format1 "Unknown query '%s'" query in
            ProtocolViolation uu____3237 in
      { qq = uu____3029; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
let read_interactive_query: FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____3250 = FStar_Util.read_line stream in
      match uu____3250 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise (ExitREPL (Prims.parse_int "0"))
      | FStar_Pervasives_Native.Some line ->
          let uu____3254 = FStar_Util.json_of_string line in
          (match uu____3254 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
let json_of_opt:
  'Auu____3267 .
    ('Auu____3267 -> FStar_Util.json) ->
      'Auu____3267 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____3285 = FStar_Util.map_option json_of_a opt_a in
      FStar_Util.dflt FStar_Util.JsonNull uu____3285
let json_of_pos: FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____3291 =
      let uu____3294 =
        let uu____3295 = FStar_Range.line_of_pos pos in
        FStar_Util.JsonInt uu____3295 in
      let uu____3296 =
        let uu____3299 =
          let uu____3300 = FStar_Range.col_of_pos pos in
          FStar_Util.JsonInt uu____3300 in
        [uu____3299] in
      uu____3294 :: uu____3296 in
    FStar_Util.JsonList uu____3291
let json_of_range_fields:
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____3310 =
          let uu____3317 =
            let uu____3324 =
              let uu____3329 = json_of_pos b in ("beg", uu____3329) in
            let uu____3330 =
              let uu____3337 =
                let uu____3342 = json_of_pos e in ("end", uu____3342) in
              [uu____3337] in
            uu____3324 :: uu____3330 in
          ("fname", (FStar_Util.JsonStr file)) :: uu____3317 in
        FStar_Util.JsonAssoc uu____3310
let json_of_use_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____3362 = FStar_Range.file_of_use_range r in
    let uu____3363 = FStar_Range.start_of_use_range r in
    let uu____3364 = FStar_Range.end_of_use_range r in
    json_of_range_fields uu____3362 uu____3363 uu____3364
let json_of_def_range: FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____3368 = FStar_Range.file_of_range r in
    let uu____3369 = FStar_Range.start_of_range r in
    let uu____3370 = FStar_Range.end_of_range r in
    json_of_range_fields uu____3368 uu____3369 uu____3370
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
    let uu____3377 =
      let uu____3384 =
        let uu____3391 =
          let uu____3398 =
            let uu____3403 =
              let uu____3404 =
                let uu____3407 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____3413 = json_of_use_range r in [uu____3413] in
                let uu____3414 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____3420 = FStar_Range.def_range r in
                      let uu____3421 = FStar_Range.use_range r in
                      uu____3420 <> uu____3421 ->
                      let uu____3422 = json_of_def_range r in [uu____3422]
                  | uu____3423 -> [] in
                FStar_List.append uu____3407 uu____3414 in
              FStar_Util.JsonList uu____3404 in
            ("ranges", uu____3403) in
          [uu____3398] in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____3391 in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____3384 in
    FStar_Util.JsonAssoc uu____3377
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
    let uu____3575 =
      let uu____3582 =
        let uu____3587 = json_of_opt json_of_def_range lr.slr_def_range in
        ("defined-at", uu____3587) in
      let uu____3588 =
        let uu____3595 =
          let uu____3600 =
            json_of_opt (fun _0_65  -> FStar_Util.JsonStr _0_65) lr.slr_typ in
          ("type", uu____3600) in
        let uu____3601 =
          let uu____3608 =
            let uu____3613 =
              json_of_opt (fun _0_66  -> FStar_Util.JsonStr _0_66) lr.slr_doc in
            ("documentation", uu____3613) in
          let uu____3614 =
            let uu____3621 =
              let uu____3626 =
                json_of_opt (fun _0_67  -> FStar_Util.JsonStr _0_67)
                  lr.slr_def in
              ("definition", uu____3626) in
            [uu____3621] in
          uu____3608 :: uu____3614 in
        uu____3595 :: uu____3601 in
      uu____3582 :: uu____3588 in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____3575
let alist_of_protocol_info:
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
  let js_features =
    let uu____3659 =
      FStar_List.map (fun _0_68  -> FStar_Util.JsonStr _0_68)
        interactive_protocol_features in
    FStar_All.pipe_left (fun _0_69  -> FStar_Util.JsonList _0_69) uu____3659 in
  [("version", js_version); ("features", js_features)]
type fstar_option_permission_level =
  | OptSet
  | OptReset
  | OptReadOnly[@@deriving show]
let uu___is_OptSet: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____3679 -> false
let uu___is_OptReset: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____3683 -> false
let uu___is_OptReadOnly: fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____3687 -> false
let string_of_option_permission_level:
  fstar_option_permission_level -> Prims.string =
  fun uu___370_3690  ->
    match uu___370_3690 with
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
  fun uu___371_3857  ->
    match uu___371_3857 with
    | FStar_Options.Const uu____3858 -> "flag"
    | FStar_Options.IntStr uu____3859 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____3860 -> "path"
    | FStar_Options.SimpleStr uu____3861 -> "string"
    | FStar_Options.EnumStr uu____3862 -> "enum"
    | FStar_Options.OpenEnumStr uu____3865 -> "open enum"
    | FStar_Options.PostProcessed (uu____3872,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____3880,typ) ->
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
        | FStar_Options.Const uu____3914 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____3927,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____3935,elem_spec) ->
            arg_snippets_of_type elem_spec in
      let uu____3941 = arg_snippets_of_type typ in
      FStar_List.map (mk_snippet name) uu____3941
let rec json_of_fstar_option_value:
  FStar_Options.option_val -> FStar_Util.json =
  fun uu___372_3946  ->
    match uu___372_3946 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____3954 = FStar_List.map json_of_fstar_option_value vs in
        FStar_Util.JsonList uu____3954
    | FStar_Options.Unset  -> FStar_Util.JsonNull
let alist_of_fstar_option:
  fstar_option ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun opt  ->
    let uu____3966 =
      let uu____3973 =
        let uu____3980 =
          let uu____3985 = json_of_fstar_option_value opt.opt_value in
          ("value", uu____3985) in
        let uu____3986 =
          let uu____3993 =
            let uu____3998 = json_of_fstar_option_value opt.opt_default in
            ("default", uu____3998) in
          let uu____3999 =
            let uu____4006 =
              let uu____4011 =
                json_of_opt (fun _0_70  -> FStar_Util.JsonStr _0_70)
                  opt.opt_documentation in
              ("documentation", uu____4011) in
            let uu____4012 =
              let uu____4019 =
                let uu____4024 =
                  let uu____4025 = kind_of_fstar_option_type opt.opt_type in
                  FStar_Util.JsonStr uu____4025 in
                ("type", uu____4024) in
              [uu____4019;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))] in
            uu____4006 :: uu____4012 in
          uu____3993 :: uu____3999 in
        uu____3980 :: uu____3986 in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3973 in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3966
let json_of_fstar_option: fstar_option -> FStar_Util.json =
  fun opt  ->
    let uu____4061 = alist_of_fstar_option opt in
    FStar_Util.JsonAssoc uu____4061
let write_json: FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____4072 = FStar_Util.string_of_json json in
     FStar_Util.print_raw uu____4072);
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
  fun uu____4128  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum in
    let js_features =
      let uu____4131 =
        FStar_List.map (fun _0_71  -> FStar_Util.JsonStr _0_71)
          interactive_protocol_features in
      FStar_Util.JsonList uu____4131 in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: alist_of_protocol_info))
let sig_of_fstar_option:
  Prims.string -> FStar_Options.opt_type -> Prims.string =
  fun name  ->
    fun typ  ->
      let flag = Prims.strcat "--" name in
      let uu____4145 = FStar_Options.desc_of_opt_type typ in
      match uu____4145 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.strcat flag (Prims.strcat " " arg_sig)
let fstar_options_list_cache: fstar_option Prims.list =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults in
  let uu____4154 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____4183  ->
            match uu____4183 with
            | (_shortname,name,typ,doc1) ->
                let uu____4198 = FStar_Util.smap_try_find defaults1 name in
                FStar_All.pipe_right uu____4198
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____4210 = sig_of_fstar_option name typ in
                        let uu____4211 = snippets_of_fstar_option name typ in
                        let uu____4214 =
                          let uu____4215 = FStar_Options.settable name in
                          if uu____4215
                          then OptSet
                          else
                            (let uu____4217 = FStar_Options.resettable name in
                             if uu____4217 then OptReset else OptReadOnly) in
                        {
                          opt_name = name;
                          opt_sig = uu____4210;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____4211;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____4214
                        })))) in
  FStar_All.pipe_right uu____4154
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
    let uu___386_4241 = opt in
    let uu____4242 = FStar_Options.get_option opt.opt_name in
    {
      opt_name = (uu___386_4241.opt_name);
      opt_sig = (uu___386_4241.opt_sig);
      opt_value = uu____4242;
      opt_default = (uu___386_4241.opt_default);
      opt_type = (uu___386_4241.opt_type);
      opt_snippets = (uu___386_4241.opt_snippets);
      opt_documentation = (uu___386_4241.opt_documentation);
      opt_permission_level = (uu___386_4241.opt_permission_level)
    }
let current_fstar_options:
  (fstar_option -> Prims.bool) -> fstar_option Prims.list =
  fun filter1  ->
    let uu____4253 = FStar_List.filter filter1 fstar_options_list_cache in
    FStar_List.map update_option uu____4253
let trim_option_name:
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun opt_name  ->
    let opt_prefix = "--" in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____4268 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix) in
      (opt_prefix, uu____4268)
    else ("", opt_name)
let json_of_repl_state: repl_state -> FStar_Util.json =
  fun st  ->
    let filenames uu____4282 =
      match uu____4282 with
      | (task,uu____4290) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | PushFragment uu____4297 -> []) in
    let uu____4298 =
      let uu____4305 =
        let uu____4310 =
          let uu____4311 =
            let uu____4314 =
              FStar_List.concatMap filenames st.repl_deps_stack in
            FStar_List.map (fun _0_72  -> FStar_Util.JsonStr _0_72)
              uu____4314 in
          FStar_Util.JsonList uu____4311 in
        ("loaded-dependencies", uu____4310) in
      let uu____4321 =
        let uu____4328 =
          let uu____4333 =
            let uu____4334 =
              let uu____4337 =
                current_fstar_options (fun uu____4342  -> true) in
              FStar_List.map json_of_fstar_option uu____4337 in
            FStar_Util.JsonList uu____4334 in
          ("options", uu____4333) in
        [uu____4328] in
      uu____4305 :: uu____4321 in
    FStar_Util.JsonAssoc uu____4298
let with_printed_effect_args:
  'Auu____4357 . (Prims.unit -> 'Auu____4357) -> 'Auu____4357 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____4369  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let term_to_string:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____4378  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____4383  -> FStar_Syntax_Print.sigelt_to_string se)
let run_exit:
  'Auu____4387 'Auu____4388 .
    'Auu____4388 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4387,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
let run_describe_protocol:
  'Auu____4416 'Auu____4417 .
    'Auu____4417 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4417,'Auu____4416) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
let run_describe_repl:
  'Auu____4444 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4444) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4461 =
      let uu____4466 = json_of_repl_state st in (QueryOK, uu____4466) in
    (uu____4461, (FStar_Util.Inl st))
let run_protocol_violation:
  'Auu____4479 'Auu____4480 .
    'Auu____4480 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4480,'Auu____4479) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
let run_generic_error:
  'Auu____4513 'Auu____4514 .
    'Auu____4514 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4514,'Auu____4513) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
let collect_errors: Prims.unit -> FStar_Errors.issue Prims.list =
  fun uu____4547  ->
    let errors = FStar_Errors.report_all () in FStar_Errors.clear (); errors
let run_segment:
  'Auu____4555 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4555) FStar_Util.either)
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
      let collect_decls uu____4582 =
        let uu____4583 = FStar_Parser_Driver.parse_fragment frag in
        match uu____4583 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____4589,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____4595,decls,uu____4597)) -> decls in
      let uu____4602 =
        with_captured_errors st.repl_env
          (fun uu____4611  ->
             let uu____4612 = collect_decls () in
             FStar_All.pipe_left
               (fun _0_73  -> FStar_Pervasives_Native.Some _0_73) uu____4612) in
      match uu____4602 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____4640 = collect_errors () in
            FStar_All.pipe_right uu____4640 (FStar_List.map json_of_issue) in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____4664 =
              let uu____4671 =
                let uu____4676 =
                  json_of_def_range (FStar_Parser_AST.decl_drange decl) in
                ("def_range", uu____4676) in
              [uu____4671] in
            FStar_Util.JsonAssoc uu____4664 in
          let js_decls =
            let uu____4686 = FStar_List.map json_of_decl decls in
            FStar_All.pipe_left (fun _0_74  -> FStar_Util.JsonList _0_74)
              uu____4686 in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
let run_vfs_add:
  'Auu____4711 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____4711) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
let run_pop:
  'Auu____4752 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4752) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4769 = nothing_left_to_pop st in
    if uu____4769
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
    let uu____4813 =
      with_captured_errors st.repl_env
        (fun _env  ->
           let uu____4839 = deps_and_repl_ld_tasks_of_our_file st.repl_fname in
           FStar_All.pipe_left
             (fun _0_75  -> FStar_Pervasives_Native.Some _0_75) uu____4839) in
    match uu____4813 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___387_4930 = st in
          let uu____4931 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1 in
          {
            repl_line = (uu___387_4930.repl_line);
            repl_column = (uu___387_4930.repl_column);
            repl_fname = (uu___387_4930.repl_fname);
            repl_deps_stack = (uu___387_4930.repl_deps_stack);
            repl_curmod = (uu___387_4930.repl_curmod);
            repl_env = uu____4931;
            repl_stdin = (uu___387_4930.repl_stdin);
            repl_names = (uu___387_4930.repl_names)
          } in
        let uu____4932 = run_repl_ld_transactions st1 tasks in
        (match uu____4932 with
         | FStar_Util.Inr st2 -> FStar_Util.Inr st2
         | FStar_Util.Inl st2 -> FStar_Util.Inl (st2, deps))
let rephrase_dependency_error: FStar_Errors.issue -> FStar_Errors.issue =
  fun issue  ->
    let uu___388_4966 = issue in
    let uu____4967 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message in
    {
      FStar_Errors.issue_message = uu____4967;
      FStar_Errors.issue_level = (uu___388_4966.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___388_4966.FStar_Errors.issue_range)
    }
let run_push_without_deps:
  'Auu____4971 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4971) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___389_4999 = st1 in
        {
          repl_line = (uu___389_4999.repl_line);
          repl_column = (uu___389_4999.repl_column);
          repl_fname = (uu___389_4999.repl_fname);
          repl_deps_stack = (uu___389_4999.repl_deps_stack);
          repl_curmod = (uu___389_4999.repl_curmod);
          repl_env =
            (let uu___390_5001 = st1.repl_env in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___390_5001.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___390_5001.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___390_5001.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___390_5001.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___390_5001.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___390_5001.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___390_5001.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___390_5001.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___390_5001.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___390_5001.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___390_5001.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___390_5001.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___390_5001.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___390_5001.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___390_5001.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___390_5001.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___390_5001.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___390_5001.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___390_5001.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___390_5001.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___390_5001.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.tc_term =
                 (uu___390_5001.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___390_5001.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___390_5001.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___390_5001.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___390_5001.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___390_5001.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___390_5001.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___390_5001.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___390_5001.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___390_5001.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___390_5001.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.dep_graph =
                 (uu___390_5001.FStar_TypeChecker_Env.dep_graph)
             });
          repl_stdin = (uu___389_4999.repl_stdin);
          repl_names = (uu___389_4999.repl_names)
        } in
      let uu____5002 = query in
      match uu____5002 with
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
            let uu____5023 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag) in
            match uu____5023 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false in
                let status =
                  if success || peek_only then QueryOK else QueryNOK in
                let json_errors =
                  let uu____5046 =
                    let uu____5049 = collect_errors () in
                    FStar_All.pipe_right uu____5049
                      (FStar_List.map json_of_issue) in
                  FStar_Util.JsonList uu____5046 in
                let st4 =
                  if success
                  then
                    let uu___391_5057 = st3 in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___391_5057.repl_fname);
                      repl_deps_stack = (uu___391_5057.repl_deps_stack);
                      repl_curmod = (uu___391_5057.repl_curmod);
                      repl_env = (uu___391_5057.repl_env);
                      repl_stdin = (uu___391_5057.repl_stdin);
                      repl_names = (uu___391_5057.repl_names)
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
       let uu____5072 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1")) in
       Prims.strcat (FStar_String.uppercase first) uu____5072)
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
          let uu____5096 = FStar_Util.psmap_empty () in
          let uu____5099 =
            let uu____5102 = FStar_Options.prims () in uu____5102 :: deps in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____5112 = FStar_Parser_Dep.lowercase_module_name dep1 in
                 FStar_Util.psmap_add acc uu____5112 true) uu____5096
            uu____5099 in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____5128  ->
               match uu____5128 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____5140 = capitalize modname in
                        FStar_Util.split uu____5140 "." in
                      let uu____5141 = loaded mod_key in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____5141 mod_path ns_query)) table
          (FStar_List.rev mods)
let run_push_with_deps:
  'Auu____5149 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5149) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      (let uu____5171 = FStar_Options.debug_any () in
       if uu____5171
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____5174 = load_deps st in
       match uu____5174 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____5207 = collect_errors () in
             FStar_List.map rephrase_dependency_error uu____5207 in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue) in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____5238 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____5238 FStar_Pervasives.ignore);
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names in
             run_push_without_deps
               (let uu___392_5241 = st1 in
                {
                  repl_line = (uu___392_5241.repl_line);
                  repl_column = (uu___392_5241.repl_column);
                  repl_fname = (uu___392_5241.repl_fname);
                  repl_deps_stack = (uu___392_5241.repl_deps_stack);
                  repl_curmod = (uu___392_5241.repl_curmod);
                  repl_env = (uu___392_5241.repl_env);
                  repl_stdin = (uu___392_5241.repl_stdin);
                  repl_names = names1
                }) query)))
let run_push:
  'Auu____5245 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5245) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let uu____5266 = nothing_left_to_pop st in
      if uu____5266
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
              (fun uu___373_5517  ->
                 match uu___373_5517 with
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
    let uu____5944 = trim_option_name opt_name in
    match uu____5944 with
    | (uu____5963,trimmed_name) ->
        let uu____5965 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name in
        (match uu____5965 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.strcat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____5993 =
               let uu____6004 =
                 let uu____6011 = update_option opt in
                 alist_of_fstar_option uu____6011 in
               ("option", uu____6004) in
             FStar_Util.Inr uu____5993)
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
      let uu____6051 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query in
      match uu____6051 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____6079 =
            let uu____6090 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info in
            ("module", uu____6090) in
          FStar_Util.Inr uu____6079
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____6114 =
            let uu____6125 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info in
            ("namespace", uu____6125) in
          FStar_Util.Inr uu____6114
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
          let uu____6194 = run_symbol_lookup st symbol pos_opt requested_info in
          match uu____6194 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____6254 ->
              let uu____6265 = run_module_lookup st symbol in
              (match uu____6265 with
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
  'Auu____6415 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6415) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____6468 =
              run_lookup' st symbol context pos_opt requested_info in
            match uu____6468 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
let code_autocomplete_mod_filter:
  'Auu____6552 .
    ('Auu____6552,FStar_Interactive_CompletionTable.mod_symbol)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____6552,FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu___374_6566  ->
    match uu___374_6566 with
    | (uu____6571,FStar_Interactive_CompletionTable.Namespace uu____6572) ->
        FStar_Pervasives_Native.None
    | (uu____6577,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____6578;
         FStar_Interactive_CompletionTable.mod_path = uu____6579;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____6586 =
          let uu____6591 =
            let uu____6592 =
              let uu___393_6593 = md in
              let uu____6594 =
                let uu____6595 =
                  FStar_Interactive_CompletionTable.mod_name md in
                Prims.strcat uu____6595 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____6594;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___393_6593.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___393_6593.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____6592 in
          (pth, uu____6591) in
        FStar_Pervasives_Native.Some uu____6586
let run_code_autocomplete:
  'Auu____6603 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6603) FStar_Util.either)
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
  'Auu____6651 'Auu____6652 'Auu____6653 .
    repl_state ->
      Prims.string ->
        'Auu____6653 ->
          'Auu____6652 ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____6651) FStar_Util.either)
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
        let uu____6714 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only") in
        match uu____6714 with
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
  'Auu____6741 'Auu____6742 .
    'Auu____6742 ->
      Prims.string ->
        Prims.bool ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            ('Auu____6742,'Auu____6741) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____6767 = trim_option_name search_term in
        match uu____6767 with
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
        | (uu____6818,uu____6819) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
let run_autocomplete:
  'Auu____6832 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____6832) FStar_Util.either)
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
  'Auu____6864 'Auu____6865 .
    repl_state ->
      (repl_state -> 'Auu____6865) ->
        ('Auu____6865,(repl_state,'Auu____6864) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun task  ->
      let env' = push st.repl_env "#compute" in
      let results =
        try
          let uu____6904 = task st in
          FStar_All.pipe_left (fun _0_77  -> FStar_Util.Inl _0_77) uu____6904
        with | e -> FStar_Util.Inr e in
      pop env' "#compute";
      (match results with
       | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st))
       | FStar_Util.Inr e -> FStar_Exn.raise e)
let run_with_parsed_and_tc_term:
  'Auu____6948 'Auu____6949 'Auu____6950 .
    repl_state ->
      Prims.string ->
        'Auu____6950 ->
          'Auu____6949 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term ->
                 (query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2)
              ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6948) FStar_Util.either)
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
                    ((uu____7034,{ FStar_Syntax_Syntax.lbname = uu____7035;
                                   FStar_Syntax_Syntax.lbunivs = univs1;
                                   FStar_Syntax_Syntax.lbtyp = uu____7037;
                                   FStar_Syntax_Syntax.lbeff = uu____7038;
                                   FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____7040);
                  FStar_Syntax_Syntax.sigrng = uu____7041;
                  FStar_Syntax_Syntax.sigquals = uu____7042;
                  FStar_Syntax_Syntax.sigmeta = uu____7043;
                  FStar_Syntax_Syntax.sigattrs = uu____7044;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____7083 -> FStar_Pervasives_Native.None in
            let parse1 frag =
              let uu____7102 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag) in
              match uu____7102 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____7108) ->
                  FStar_Pervasives_Native.Some decls
              | uu____7133 -> FStar_Pervasives_Native.None in
            let desugar env decls =
              let uu____7147 =
                let uu____7152 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls in
                uu____7152 env.FStar_TypeChecker_Env.dsenv in
              FStar_Pervasives_Native.fst uu____7147 in
            let typecheck tcenv decls =
              let uu____7170 = FStar_TypeChecker_Tc.tc_decls tcenv decls in
              match uu____7170 with | (ses,uu____7184,uu____7185) -> ses in
            run_and_rewind st
              (fun st1  ->
                 let tcenv = st1.repl_env in
                 let frag = dummy_let_fragment term in
                 match st1.repl_curmod with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                 | uu____7208 ->
                     let uu____7209 = parse1 frag in
                     (match uu____7209 with
                      | FStar_Pervasives_Native.None  ->
                          (QueryNOK,
                            (FStar_Util.JsonStr "Could not parse this term"))
                      | FStar_Pervasives_Native.Some decls ->
                          let aux uu____7232 =
                            let decls1 = desugar tcenv decls in
                            let ses = typecheck tcenv decls1 in
                            match find_let_body ses with
                            | FStar_Pervasives_Native.None  ->
                                (QueryNOK,
                                  (FStar_Util.JsonStr
                                     "Typechecking yielded an unexpected term"))
                            | FStar_Pervasives_Native.Some (univs1,def) ->
                                let uu____7267 =
                                  FStar_Syntax_Subst.open_univ_vars univs1
                                    def in
                                (match uu____7267 with
                                 | (univs2,def1) ->
                                     let tcenv1 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         tcenv univs2 in
                                     continuation tcenv1 def1) in
                          let uu____7279 = FStar_Options.trace_error () in
                          if uu____7279
                          then aux ()
                          else
                            (try aux ()
                             with
                             | e ->
                                 let uu____7304 =
                                   let uu____7305 =
                                     FStar_Errors.issue_of_exn e in
                                   match uu____7305 with
                                   | FStar_Pervasives_Native.Some issue ->
                                       let uu____7309 =
                                         FStar_Errors.format_issue issue in
                                       FStar_Util.JsonStr uu____7309
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Exn.raise e in
                                 (QueryNOK, uu____7304))))
let run_compute:
  'Auu____7314 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____7314) FStar_Util.either)
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
               let uu____7377 =
                 let uu____7378 = term_to_string tcenv normalized in
                 FStar_Util.JsonStr uu____7378 in
               (QueryOK, uu____7377))
type search_term' =
  | NameContainsStr of Prims.string
  | TypeContainsLid of FStar_Ident.lid[@@deriving show]
and search_term = {
  st_negate: Prims.bool;
  st_term: search_term';}[@@deriving show]
let uu___is_NameContainsStr: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____7399 -> false
let __proj__NameContainsStr__item___0: search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0
let uu___is_TypeContainsLid: search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____7411 -> false
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
  fun uu___375_7431  ->
    match uu___375_7431 with
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
    let uu____7595 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    let uu____7602 = FStar_Util.mk_ref FStar_Pervasives_Native.None in
    { sc_lid = lid; sc_typ = uu____7595; sc_fvars = uu____7602 }
let sc_typ:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____7649 = FStar_ST.op_Bang sc.sc_typ in
      match uu____7649 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____7706 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid in
            match uu____7706 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7727,typ),uu____7729) ->
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
      let uu____7803 = FStar_ST.op_Bang sc.sc_fvars in
      match uu____7803 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____7874 = sc_typ tcenv sc in
            FStar_Syntax_Free.fvars uu____7874 in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
let json_of_search_result:
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____7939 = sc_typ tcenv sc in term_to_string tcenv uu____7939 in
      let uu____7940 =
        let uu____7947 =
          let uu____7952 =
            let uu____7953 =
              let uu____7954 =
                FStar_ToSyntax_Env.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid in
              uu____7954.FStar_Ident.str in
            FStar_Util.JsonStr uu____7953 in
          ("lid", uu____7952) in
        [uu____7947; ("type", (FStar_Util.JsonStr typ_str))] in
      FStar_Util.JsonAssoc uu____7940
exception InvalidSearch of Prims.string
let uu___is_InvalidSearch: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____7973 -> true
    | uu____7974 -> false
let __proj__InvalidSearch__item__uu___: Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____7981 -> uu____7981
let run_search:
  'Auu____7985 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____7985) FStar_Util.either)
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
              let uu____8020 = sc_fvars tcenv candidate in
              FStar_Util.set_mem lid uu____8020 in
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
              let uu____8044 =
                let uu____8045 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1 in
                InvalidSearch uu____8045 in
              FStar_Exn.raise uu____8044
            else
              if beg_quote
              then
                (let uu____8047 = strip_quotes term1 in
                 NameContainsStr uu____8047)
              else
                (let lid = FStar_Ident.lid_of_str term1 in
                 let uu____8050 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid in
                 match uu____8050 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____8053 =
                       let uu____8054 =
                         FStar_Util.format1 "Unknown identifier: %s" term1 in
                       InvalidSearch uu____8054 in
                     FStar_Exn.raise uu____8053
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1) in
          { st_negate = negate; st_term = parsed } in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ") in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term) in
        FStar_Util.sort_with cmp terms in
      let pprint_one term =
        let uu____8070 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str in
        Prims.strcat (if term.st_negate then "-" else "") uu____8070 in
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
                let uu____8133 = FStar_List.map pprint_one terms in
                FStar_Util.concat_l " " uu____8133 in
              let uu____8136 =
                let uu____8137 =
                  FStar_Util.format1 "No results found for query [%s]" kwds in
                InvalidSearch uu____8137 in
              FStar_Exn.raise uu____8136
          | uu____8142 -> (QueryOK, (FStar_Util.JsonList js))
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
          { push_kind = SyntaxCheck ; push_code = uu____8232;
            push_line = uu____8233; push_column = uu____8234;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____8235 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____8236 -> q)
let rec go: repl_state -> Prims.int =
  fun st  ->
    let rec loop st1 =
      let query =
        let uu____8245 = read_interactive_query st1.repl_stdin in
        validate_query st1 uu____8245 in
      let uu____8246 = run_query st1 query.qq in
      match uu____8246 with
      | ((status,response),state_opt) ->
          (write_response query.qid status response;
           (match state_opt with
            | FStar_Util.Inl st' -> loop st'
            | FStar_Util.Inr exitcode -> FStar_Exn.raise (ExitREPL exitcode))) in
    let uu____8277 = FStar_Options.trace_error () in
    if uu____8277 then loop st else (try loop st with | ExitREPL n1 -> n1)
let interactive_error_handler: FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref [] in
  let add_one1 e =
    let uu____8296 =
      let uu____8299 = FStar_ST.op_Bang issues in e :: uu____8299 in
    FStar_ST.op_Colon_Equals issues uu____8296 in
  let count_errors uu____8433 =
    let uu____8434 =
      let uu____8437 = FStar_ST.op_Bang issues in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____8437 in
    FStar_List.length uu____8434 in
  let report1 uu____8511 =
    let uu____8512 = FStar_ST.op_Bang issues in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8512 in
  let clear1 uu____8582 = FStar_ST.op_Colon_Equals issues [] in
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
             let uu____8669 = get_json () in write_message label1 uu____8669)
  }
let initial_range: FStar_Range.range =
  let uu____8670 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  let uu____8671 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0") in
  FStar_Range.mk_range "<input>" uu____8670 uu____8671
let interactive_mode': Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps in
     let env1 = FStar_TypeChecker_Env.set_range env initial_range in
     let init_st =
       let uu____8679 = FStar_Util.open_stdin () in
       {
         repl_line = (Prims.parse_int "1");
         repl_column = (Prims.parse_int "0");
         repl_fname = filename;
         repl_deps_stack = [];
         repl_curmod = FStar_Pervasives_Native.None;
         repl_env = env1;
         repl_stdin = uu____8679;
         repl_names = FStar_Interactive_CompletionTable.empty
       } in
     let exit_code =
       let uu____8685 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ()) in
       if uu____8685
       then
         let uu____8686 =
           let uu____8687 = FStar_Options.file_list () in
           FStar_List.hd uu____8687 in
         FStar_SMTEncoding_Solver.with_hints_db uu____8686
           (fun uu____8691  -> go init_st)
       else go init_st in
     FStar_All.exit exit_code)
let interactive_mode: Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    (let uu____8698 =
       let uu____8699 = FStar_Options.codegen () in
       FStar_Option.isSome uu____8699 in
     if uu____8698
     then
       FStar_Errors.maybe_fatal_error FStar_Range.dummyRange
         (FStar_Errors.IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let uu____8703 = FStar_Options.trace_error () in
     if uu____8703
     then interactive_mode' filename
     else
       (try
          FStar_Errors.set_handler interactive_error_handler;
          interactive_mode' filename
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))