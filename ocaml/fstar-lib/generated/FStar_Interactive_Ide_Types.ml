open Prims
let (initial_range : FStar_Compiler_Range_Type.range) =
  let uu___ = FStar_Compiler_Range_Type.mk_pos Prims.int_one Prims.int_zero in
  let uu___1 = FStar_Compiler_Range_Type.mk_pos Prims.int_one Prims.int_zero in
  FStar_Compiler_Range_Type.mk_range "<input>" uu___ uu___1
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKCode -> true | uu___ -> false
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKOption _0 -> true | uu___ -> false
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee -> match projectee with | CKOption _0 -> _0
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee ->
    match projectee with | CKModuleOrNamespace _0 -> true | uu___ -> false
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee -> match projectee with | CKModuleOrNamespace _0 -> _0
type lookup_context =
  | LKSymbolOnly 
  | LKModule 
  | LKOption 
  | LKCode 
let (uu___is_LKSymbolOnly : lookup_context -> Prims.bool) =
  fun projectee ->
    match projectee with | LKSymbolOnly -> true | uu___ -> false
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee -> match projectee with | LKModule -> true | uu___ -> false
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee -> match projectee with | LKOption -> true | uu___ -> false
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee -> match projectee with | LKCode -> true | uu___ -> false
type position = (Prims.string * Prims.int * Prims.int)
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
type push_query =
  {
  push_kind: push_kind ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool ;
  push_code_or_decl:
    (Prims.string,
      (FStar_Parser_AST.decl * FStar_Parser_ParseIt.code_fragment))
      FStar_Pervasives.either
    }
let (__proj__Mkpush_query__item__push_kind : push_query -> push_kind) =
  fun projectee ->
    match projectee with
    | { push_kind = push_kind1; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_kind1
let (__proj__Mkpush_query__item__push_line : push_query -> Prims.int) =
  fun projectee ->
    match projectee with
    | { push_kind = push_kind1; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_line
let (__proj__Mkpush_query__item__push_column : push_query -> Prims.int) =
  fun projectee ->
    match projectee with
    | { push_kind = push_kind1; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_column
let (__proj__Mkpush_query__item__push_peek_only : push_query -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { push_kind = push_kind1; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_peek_only
let (__proj__Mkpush_query__item__push_code_or_decl :
  push_query ->
    (Prims.string,
      (FStar_Parser_AST.decl * FStar_Parser_ParseIt.code_fragment))
      FStar_Pervasives.either)
  =
  fun projectee ->
    match projectee with
    | { push_kind = push_kind1; push_line; push_column; push_peek_only;
        push_code_or_decl;_} -> push_code_or_decl
type lookup_symbol_range = FStar_Json.json
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let (uu___is_QueryOK : query_status -> Prims.bool) =
  fun projectee -> match projectee with | QueryOK -> true | uu___ -> false
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee -> match projectee with | QueryNOK -> true | uu___ -> false
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee ->
    match projectee with | QueryViolatesProtocol -> true | uu___ -> false
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
type optmod_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type timed_fname =
  {
  tf_fname: Prims.string ;
  tf_modtime: FStar_Compiler_Util.time }
let (__proj__Mktimed_fname__item__tf_fname : timed_fname -> Prims.string) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_fname
let (__proj__Mktimed_fname__item__tf_modtime :
  timed_fname -> FStar_Compiler_Util.time) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_modtime
type repl_task =
  | LDInterleaved of (timed_fname * timed_fname) 
  | LDSingle of timed_fname 
  | LDInterfaceOfCurrentFile of timed_fname 
  | PushFragment of ((FStar_Parser_ParseIt.input_frag, FStar_Parser_AST.decl)
  FStar_Pervasives.either * push_kind * FStar_Json.json Prims.list) 
  | Noop 
let (uu___is_LDInterleaved : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDInterleaved _0 -> true | uu___ -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu___ -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu___ -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu___ -> false
let (__proj__PushFragment__item___0 :
  repl_task ->
    ((FStar_Parser_ParseIt.input_frag, FStar_Parser_AST.decl)
      FStar_Pervasives.either * push_kind * FStar_Json.json Prims.list))
  = fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu___ -> false
type full_buffer_request_kind =
  | Full 
  | Lax 
  | Cache 
  | ReloadDeps 
  | VerifyToPosition of position 
  | LaxToPosition of position 
let (uu___is_Full : full_buffer_request_kind -> Prims.bool) =
  fun projectee -> match projectee with | Full -> true | uu___ -> false
let (uu___is_Lax : full_buffer_request_kind -> Prims.bool) =
  fun projectee -> match projectee with | Lax -> true | uu___ -> false
let (uu___is_Cache : full_buffer_request_kind -> Prims.bool) =
  fun projectee -> match projectee with | Cache -> true | uu___ -> false
let (uu___is_ReloadDeps : full_buffer_request_kind -> Prims.bool) =
  fun projectee -> match projectee with | ReloadDeps -> true | uu___ -> false
let (uu___is_VerifyToPosition : full_buffer_request_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | VerifyToPosition _0 -> true | uu___ -> false
let (__proj__VerifyToPosition__item___0 :
  full_buffer_request_kind -> position) =
  fun projectee -> match projectee with | VerifyToPosition _0 -> _0
let (uu___is_LaxToPosition : full_buffer_request_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | LaxToPosition _0 -> true | uu___ -> false
let (__proj__LaxToPosition__item___0 : full_buffer_request_kind -> position)
  = fun projectee -> match projectee with | LaxToPosition _0 -> _0
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
  FStar_Pervasives_Native.option * Prims.string Prims.list *
  lookup_symbol_range FStar_Pervasives_Native.option) 
  | Compute of (Prims.string * FStar_TypeChecker_Env.step Prims.list
  FStar_Pervasives_Native.option) 
  | Search of Prims.string 
  | GenericError of Prims.string 
  | ProtocolViolation of Prims.string 
  | FullBuffer of (Prims.string * full_buffer_request_kind * Prims.bool) 
  | Callback of
  (repl_state ->
     ((query_status * FStar_Json.json Prims.list) * (repl_state, Prims.int)
       FStar_Pervasives.either))
  
  | Format of Prims.string 
  | RestartSolver 
  | Cancel of position FStar_Pervasives_Native.option 
and query = {
  qq: query' ;
  qid: Prims.string }
and repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_fname: Prims.string ;
  repl_deps_stack: (repl_depth_t * (repl_task * repl_state)) Prims.list ;
  repl_curmod: optmod_t ;
  repl_env: FStar_TypeChecker_Env.env ;
  repl_stdin: FStar_Compiler_Util.stream_reader ;
  repl_names: FStar_Interactive_CompletionTable.table ;
  repl_buffered_input_queries: query Prims.list }
let (uu___is_Exit : query' -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu___ -> false
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeProtocol -> true | uu___ -> false
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | DescribeRepl -> true | uu___ -> false
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee -> match projectee with | Segment _0 -> true | uu___ -> false
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Segment _0 -> _0
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee -> match projectee with | Pop -> true | uu___ -> false
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee -> match projectee with | Push _0 -> true | uu___ -> false
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee -> match projectee with | Push _0 -> _0
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee -> match projectee with | VfsAdd _0 -> true | uu___ -> false
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee -> match projectee with | VfsAdd _0 -> _0
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | AutoComplete _0 -> true | uu___ -> false
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee -> match projectee with | AutoComplete _0 -> _0
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee -> match projectee with | Lookup _0 -> true | uu___ -> false
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list * lookup_symbol_range
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Lookup _0 -> _0
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee -> match projectee with | Compute _0 -> true | uu___ -> false
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Compute _0 -> _0
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee -> match projectee with | Search _0 -> true | uu___ -> false
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Search _0 -> _0
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | GenericError _0 -> true | uu___ -> false
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | GenericError _0 -> _0
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | ProtocolViolation _0 -> true | uu___ -> false
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | ProtocolViolation _0 -> _0
let (uu___is_FullBuffer : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | FullBuffer _0 -> true | uu___ -> false
let (__proj__FullBuffer__item___0 :
  query' -> (Prims.string * full_buffer_request_kind * Prims.bool)) =
  fun projectee -> match projectee with | FullBuffer _0 -> _0
let (uu___is_Callback : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | Callback _0 -> true | uu___ -> false
let (__proj__Callback__item___0 :
  query' ->
    repl_state ->
      ((query_status * FStar_Json.json Prims.list) * (repl_state, Prims.int)
        FStar_Pervasives.either))
  = fun projectee -> match projectee with | Callback _0 -> _0
let (uu___is_Format : query' -> Prims.bool) =
  fun projectee -> match projectee with | Format _0 -> true | uu___ -> false
let (__proj__Format__item___0 : query' -> Prims.string) =
  fun projectee -> match projectee with | Format _0 -> _0
let (uu___is_RestartSolver : query' -> Prims.bool) =
  fun projectee ->
    match projectee with | RestartSolver -> true | uu___ -> false
let (uu___is_Cancel : query' -> Prims.bool) =
  fun projectee -> match projectee with | Cancel _0 -> true | uu___ -> false
let (__proj__Cancel__item___0 :
  query' -> position FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Cancel _0 -> _0
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee -> match projectee with | { qq; qid;_} -> qq
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee -> match projectee with | { qq; qid;_} -> qid
let (__proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_line
let (__proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_column
let (__proj__Mkrepl_state__item__repl_fname : repl_state -> Prims.string) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_fname
let (__proj__Mkrepl_state__item__repl_deps_stack :
  repl_state -> (repl_depth_t * (repl_task * repl_state)) Prims.list) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_deps_stack
let (__proj__Mkrepl_state__item__repl_curmod : repl_state -> optmod_t) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_curmod
let (__proj__Mkrepl_state__item__repl_env :
  repl_state -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_env
let (__proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Compiler_Util.stream_reader) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_stdin
let (__proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_names
let (__proj__Mkrepl_state__item__repl_buffered_input_queries :
  repl_state -> query Prims.list) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names; repl_buffered_input_queries;_} ->
        repl_buffered_input_queries
type callback_t =
  repl_state ->
    ((query_status * FStar_Json.json Prims.list) * (repl_state, Prims.int)
      FStar_Pervasives.either)
type repl_stack_entry_t = (repl_depth_t * (repl_task * repl_state))
type repl_stack_t = (repl_depth_t * (repl_task * repl_state)) Prims.list
type grepl_state =
  {
  grepl_repls: repl_state FStar_Compiler_Util.psmap ;
  grepl_stdin: FStar_Compiler_Util.stream_reader }
let (__proj__Mkgrepl_state__item__grepl_repls :
  grepl_state -> repl_state FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_repls
let (__proj__Mkgrepl_state__item__grepl_stdin :
  grepl_state -> FStar_Compiler_Util.stream_reader) =
  fun projectee ->
    match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_stdin
let (t0 : FStar_Compiler_Util.time) = FStar_Compiler_Util.now ()
let (dummy_tf_of_fname : Prims.string -> timed_fname) =
  fun fname -> { tf_fname = fname; tf_modtime = t0 }
let (string_of_timed_fname : timed_fname -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Compiler_Util.format1 "{ %s }" fname
        else
          (let uu___2 = FStar_Compiler_Util.string_of_time modtime in
           FStar_Compiler_Util.format2 "{ %s; %s }" fname uu___2)
let (string_of_repl_task : repl_task -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | LDInterleaved (intf, impl) ->
        let uu___1 = string_of_timed_fname intf in
        let uu___2 = string_of_timed_fname impl in
        FStar_Compiler_Util.format2 "LDInterleaved (%s, %s)" uu___1 uu___2
    | LDSingle intf_or_impl ->
        let uu___1 = string_of_timed_fname intf_or_impl in
        FStar_Compiler_Util.format1 "LDSingle %s" uu___1
    | LDInterfaceOfCurrentFile intf ->
        let uu___1 = string_of_timed_fname intf in
        FStar_Compiler_Util.format1 "LDInterfaceOfCurrentFile %s" uu___1
    | PushFragment (FStar_Pervasives.Inl frag, uu___1, uu___2) ->
        FStar_Compiler_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
    | PushFragment (FStar_Pervasives.Inr d, uu___1, uu___2) ->
        let uu___3 = FStar_Parser_AST.decl_to_string d in
        FStar_Compiler_Util.format1 "PushFragment { decl = %s }" uu___3
    | Noop -> "Noop {}"
let (string_of_repl_stack_entry : repl_stack_entry_t -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | ((depth, i), (task, state)) ->
        let uu___1 =
          let uu___2 = FStar_Compiler_Util.string_of_int i in
          let uu___3 = let uu___4 = string_of_repl_task task in [uu___4] in
          uu___2 :: uu___3 in
        FStar_Compiler_Util.format "{depth=%s; task=%s}" uu___1
let (string_of_repl_stack : repl_stack_entry_t Prims.list -> Prims.string) =
  fun s ->
    let uu___ = FStar_Compiler_List.map string_of_repl_stack_entry s in
    FStar_String.concat ";\n\t\t" uu___
let (repl_state_to_string : repl_state -> Prims.string) =
  fun r ->
    let uu___ =
      let uu___1 = FStar_Compiler_Util.string_of_int r.repl_line in
      let uu___2 =
        let uu___3 = FStar_Compiler_Util.string_of_int r.repl_column in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              match r.repl_curmod with
              | FStar_Pervasives_Native.None -> "None"
              | FStar_Pervasives_Native.Some m ->
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
            let uu___7 =
              let uu___8 = string_of_repl_stack r.repl_deps_stack in [uu___8] in
            uu___6 :: uu___7 in
          (r.repl_fname) :: uu___5 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Compiler_Util.format
      "{\n\trepl_line=%s;\n\trepl_column=%s;\n\trepl_fname=%s;\n\trepl_cur_mod=%s;\n\t\\      \n      repl_deps_stack={%s}\n}"
      uu___
let (push_query_to_string : push_query -> Prims.string) =
  fun pq ->
    let pk =
      match pq.push_kind with
      | SyntaxCheck -> "SyntaxCheck"
      | LaxCheck -> "LaxCheck"
      | FullCheck -> "FullCheck" in
    let code_or_decl =
      match pq.push_code_or_decl with
      | FStar_Pervasives.Inl code -> code
      | FStar_Pervasives.Inr (_decl, code) -> code.FStar_Parser_ParseIt.code in
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Compiler_Util.string_of_int pq.push_line in
        let uu___3 =
          let uu___4 = FStar_Compiler_Util.string_of_int pq.push_column in
          let uu___5 =
            let uu___6 = FStar_Compiler_Util.string_of_bool pq.push_peek_only in
            [uu___6; code_or_decl] in
          uu___4 :: uu___5 in
        uu___2 :: uu___3 in
      pk :: uu___1 in
    FStar_Compiler_Util.format
      "{ push_kind = %s; push_line = %s; push_column = %s; push_peek_only = %s; push_code_or_decl = %s }"
      uu___
let (query_to_string : query -> Prims.string) =
  fun q ->
    match q.qq with
    | Exit -> "Exit"
    | DescribeProtocol -> "DescribeProtocol"
    | DescribeRepl -> "DescribeRepl"
    | Segment uu___ -> "Segment"
    | Pop -> "Pop"
    | Push pq ->
        let uu___ =
          let uu___1 = push_query_to_string pq in Prims.op_Hat uu___1 ")" in
        Prims.op_Hat "(Push " uu___
    | VfsAdd uu___ -> "VfsAdd"
    | AutoComplete uu___ -> "AutoComplete"
    | Lookup (s, _lc, pos, features, _sr) ->
        let uu___ =
          match pos with
          | FStar_Pervasives_Native.None -> "None"
          | FStar_Pervasives_Native.Some (f, i, j) ->
              let uu___1 = FStar_Compiler_Util.string_of_int i in
              let uu___2 = FStar_Compiler_Util.string_of_int j in
              FStar_Compiler_Util.format3 "(%s, %s, %s)" f uu___1 uu___2 in
        FStar_Compiler_Util.format3 "(Lookup %s %s [%s])" s uu___
          (FStar_String.concat "; " features)
    | Compute uu___ -> "Compute"
    | Search uu___ -> "Search"
    | GenericError uu___ -> "GenericError"
    | ProtocolViolation uu___ -> "ProtocolViolation"
    | FullBuffer uu___ -> "FullBuffer"
    | Callback uu___ -> "Callback"
    | Format uu___ -> "Format"
    | RestartSolver -> "RestartSolver"
    | Cancel uu___ -> "Cancel"
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | Exit -> false
    | DescribeProtocol -> false
    | DescribeRepl -> false
    | Segment uu___1 -> false
    | Pop -> false
    | Push
        { push_kind = uu___1; push_line = uu___2; push_column = uu___3;
          push_peek_only = false; push_code_or_decl = uu___4;_}
        -> false
    | VfsAdd uu___1 -> false
    | GenericError uu___1 -> false
    | ProtocolViolation uu___1 -> false
    | FullBuffer uu___1 -> false
    | Callback uu___1 -> false
    | Format uu___1 -> false
    | RestartSolver -> false
    | Cancel uu___1 -> false
    | Push uu___1 -> true
    | AutoComplete uu___1 -> true
    | Lookup uu___1 -> true
    | Compute uu___1 -> true
    | Search uu___1 -> true
let (interactive_protocol_vernum : Prims.int) = (Prims.of_int (2))
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
  "progress";
  "full-buffer";
  "format";
  "restart-solver";
  "cancel"]
let (json_of_issue_level : FStar_Errors.issue_level -> FStar_Json.json) =
  fun i ->
    FStar_Json.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented -> "not-implemented"
       | FStar_Errors.EInfo -> "info"
       | FStar_Errors.EWarning -> "warning"
       | FStar_Errors.EError -> "error")
let (json_of_issue : FStar_Errors.issue -> FStar_Json.json) =
  fun issue ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStar_Errors.issue_message issue in
              FStar_Json.JsonStr uu___5 in
            ("message", uu___4) in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.None -> []
                    | FStar_Pervasives_Native.Some r ->
                        let uu___9 =
                          FStar_Compiler_Range_Ops.json_of_use_range r in
                        [uu___9] in
                  let uu___9 =
                    match issue.FStar_Errors.issue_range with
                    | FStar_Pervasives_Native.Some r when
                        let uu___10 = FStar_Compiler_Range_Type.def_range r in
                        let uu___11 = FStar_Compiler_Range_Type.use_range r in
                        uu___10 <> uu___11 ->
                        let uu___10 =
                          FStar_Compiler_Range_Ops.json_of_def_range r in
                        [uu___10]
                    | uu___10 -> [] in
                  FStar_Compiler_List.op_At uu___8 uu___9 in
                FStar_Json.JsonList uu___7 in
              ("ranges", uu___6) in
            [uu___5] in
          uu___3 :: uu___4 in
        FStar_Compiler_List.op_At
          (match issue.FStar_Errors.issue_number with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some n ->
               [("number", (FStar_Json.JsonInt n))]) uu___2 in
      FStar_Compiler_List.op_At
        [("level", (json_of_issue_level issue.FStar_Errors.issue_level))]
        uu___1 in
    FStar_Compiler_Effect.op_Less_Bar
      (fun uu___1 -> FStar_Json.JsonAssoc uu___1) uu___
let (js_pushkind : FStar_Json.json -> push_kind) =
  fun s ->
    let uu___ = FStar_Interactive_JsonHelper.js_str s in
    match uu___ with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu___1 -> FStar_Interactive_JsonHelper.js_fail "push_kind" s
let (js_reductionrule : FStar_Json.json -> FStar_TypeChecker_Env.step) =
  fun s ->
    let uu___ = FStar_Interactive_JsonHelper.js_str s in
    match uu___ with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu___1 -> FStar_Interactive_JsonHelper.js_fail "reduction rule" s
let (js_optional_completion_context :
  FStar_Json.json FStar_Pervasives_Native.option -> completion_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu___ = FStar_Interactive_JsonHelper.js_str k1 in
        (match uu___ with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu___1 ->
             FStar_Interactive_JsonHelper.js_fail
               "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
let (js_optional_lookup_context :
  FStar_Json.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k ->
    match k with
    | FStar_Pervasives_Native.None -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu___ = FStar_Interactive_JsonHelper.js_str k1 in
        (match uu___ with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu___1 ->
             FStar_Interactive_JsonHelper.js_fail
               "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)